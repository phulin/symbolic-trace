{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances, CPP #-}
module Memlog(MemlogOp(..), AddrOp(..), AddrEntry(..), AddrEntryType(..), AddrFlag(..), parseMemlog, associateFuncs, shouldIgnoreInst, pairListFind, InstOpList, MemlogList) where

import Control.Applicative
import Control.Monad(liftM)
#ifdef DEBUG
import Control.Monad.Error
#endif
import Control.Monad.State
import Control.Monad.Trans(lift)
import Control.Monad.Trans.Maybe
import Data.Binary.Get(Get, runGet, getWord32host, getWord64host, skip, getLazyByteString)
import Data.Bits(shiftR, (.&.))
import Data.LLVM.Types
import Data.Maybe(isJust, fromMaybe, catMaybes)
import Data.Word(Word8, Word32, Word64)
import Text.Printf(printf)
import Debug.Trace

import qualified Data.ByteString.Lazy as B
import qualified Data.Char as C
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T

import Data.RESET.Types
import AppList
import Instances
import Pretty

instance Pretty AddrEntry where
    pretty AddrEntry{ addrType = MAddr, addrVal = val }
        = printf "0x%08x" val
    pretty AddrEntry{ addrType = GReg, addrVal = reg } = case reg of
        0 -> "EAX"
        1 -> "ECX"
        2 -> "EDX"
        3 -> "EBX"
        4 -> "ESP"
        5 -> "EBP"
        6 -> "ESI"
        7 -> "EDI"
        _ -> "Reg" ++ show reg
    pretty addr = show addr

parseMemlog :: FilePath -> IO [MemlogOp]
parseMemlog file = runGet (getTubtfHeader >> many getMemlogEntry) <$> B.readFile file

getTubtfHeader :: Get ()
getTubtfHeader = do
    skip 4 -- tubtf version
    colw <- getWord32host
    case colw of
        0 -> error "Can't process 32-bit tubtf log"
        1 -> return () -- 64-bit, so we're good.
    skip 8 -- FIXME: we currently ignore what elements are present - we should check that.
    skip 4 -- number of rows; we'll just read until EOF.

word :: Get Word64
word = getWord64host

getMemlogEntry :: Get MemlogOp
getMemlogEntry = do
    cr3 <- word
    eip <- word
    entryType <- word
    out <- case entryType of
        30 -> BeginBlockOp eip <$> word <* skip 24
        31 -> MemoryOp LoadOp <$> getAddrEntry
        32 -> MemoryOp StoreOp <$> getAddrEntry
        33 -> BranchOp <$> word <* skip 24
        34 -> SelectOp <$> word <* skip 24
        35 -> SwitchOp <$> word <* skip 24
        36 -> ExceptionOp <$ skip 32
        _ -> do
            nextBytes <- getLazyByteString 32
            error $ printf "Unknown entry type %d; next bytes %s" entryType
                (L.concatMap (printf "%x " :: Word8 -> String) $ B.unpack nextBytes)
    return out

getAddrEntry :: Get AddrEntry
getAddrEntry = do
    metadata <- word
    let typ = toEnum $ fromIntegral $ metadata .&. 0xff
        flagNum = metadata `shiftR` 8 .&. 0xff
    flag <- case flagNum of
        5 -> return IrrelevantFlag
        0 -> return NoFlag
        1 -> return ExceptionFlag
        2 -> return ReadlogFlag
        3 -> return FuncargFlag
        f -> error ("Parse error in dynamic log: Unexpected flag " ++ show f)
    val <- word
    skip 24
    return $ t $ AddrEntry typ val flag

type MemlogAppList = AppList (BasicBlock, InstOpList)

-- Monads for doing the association.

data MemlogState = MemlogState{
    memlogOpStream :: [MemlogOp],
    -- Work already done in current block. We use this instead of a mapM so we
    -- can do better error reporting.
    memlogCurrentAssociated :: AppList (Instruction, Maybe MemlogOp),
    -- Already associated blocks. If the Maybe is Nothing, we don't keep track
    -- (i.e. this is loading code, not something we're actually interested in)
    memlogAssociatedBlocks :: Maybe MemlogAppList,
    memlogNextBlock :: Maybe BasicBlock, -- Next block to process
    memlogSkipRest :: Bool,
    memlogBlockMap :: M.Map Word64 Function
}

noMemlogState :: MemlogState
noMemlogState = MemlogState{
    memlogOpStream = [],
    memlogCurrentAssociated = mkAppList,
    memlogAssociatedBlocks = Just mkAppList,
    memlogNextBlock = Nothing,
    memlogSkipRest = False,
    memlogBlockMap = M.empty
}

class (Functor m, Monad m, MonadState MemlogState m) => Memlogish m where
instance (Functor m, Monad m, MonadState MemlogState m) => Memlogish m

type MemlogContext = State MemlogState

#ifdef DEBUG
type FuncOpContext = ErrorT String MemlogContext
#else
type FuncOpContext = MemlogContext

runErrorT = liftM Right
throwError s = fail s
catchError c h = c
#endif

getOpStream :: Memlogish m => m [MemlogOp]
getOpStream = memlogOpStream <$> get
putOpStream :: Memlogish m => [MemlogOp] -> m ()
putOpStream stream = modify (\s -> s{ memlogOpStream = stream })

memlogPopMaybe :: Memlogish m => m (Maybe MemlogOp)
memlogPopMaybe = do
    stream <- getOpStream
    case stream of
        op : ops -> putOpStream ops >> return (Just op)
        [] -> return Nothing

memlogPopErr :: Memlogish m => Instruction -> m MemlogOp
memlogPopErr inst = fromMaybe err <$> memlogPopMaybe
    where err = error $ printf "Failed on block %s"
              (show $ instructionBasicBlock inst)

putNextBlock :: Memlogish m => BasicBlock -> m ()
putNextBlock block = modify (\s -> s{ memlogNextBlock = Just block })
clearNextBlock :: Memlogish m => m ()
clearNextBlock = modify (\s -> s{ memlogNextBlock = Nothing })

clearCurrentAssociated :: Memlogish m => m ()
clearCurrentAssociated = modify (\s -> s{ memlogCurrentAssociated = mkAppList })
appendInstOp :: Memlogish m => (Instruction, Maybe MemlogOp) -> m ()
appendInstOp instOp
    = modify (\s -> s{
        memlogCurrentAssociated = memlogCurrentAssociated s +: instOp })

appendAssociated :: Memlogish m => (BasicBlock, InstOpList) -> m ()
appendAssociated block = do
    associated <- memlogAssociatedBlocks <$> get
    case associated of
        Nothing -> return ()
        Just associated' ->
            modify (\s -> s{ memlogAssociatedBlocks = Just $ associated' +: block })

skipRest :: Memlogish m => m ()
skipRest = modify (\s -> s{ memlogSkipRest = True })

t x = traceShow x x

associateBasicBlock :: BasicBlock -> FuncOpContext InstOpList
associateBasicBlock block = do
    clearCurrentAssociated
    clearNextBlock
    modify (\s -> s{ memlogSkipRest = False })
    mapM associateInstWithCopy $ basicBlockInstructions block
    where associateInstWithCopy inst = do
              skip <- memlogSkipRest <$> get
              case skip of
                  True -> return (inst, Nothing)
                  False -> do
                      maybeOp <- associateInst inst `catchError` handler inst
                      appendInstOp (inst, maybeOp)
                      return (inst, maybeOp)
          handler :: Instruction -> String -> FuncOpContext (Maybe MemlogOp)
          handler inst err = do
              ops <- getOpStream
              currentAssociated <- memlogCurrentAssociated <$> get
              Just associatedBlocks <- memlogAssociatedBlocks <$> get
              throwError $ printf
                  ("Error during alignment.\n\n" ++
                      "Previous block:\n%s\n\nCurrent block:\n%s\n%s\n\n" ++
                      "Next ops:\n%s\n\nError: %s")
                  (L.intercalate "\n\n" $ map showBlock $ suffix 1 associatedBlocks)
                  (showBlock (block, unAppList currentAssociated))
                  (show inst)
                  (L.intercalate "\n" $ map show $ take 5 ops)
                  err

shouldIgnoreInst :: Instruction -> Bool
shouldIgnoreInst AllocaInst{} = True
shouldIgnoreInst CallInst{ callFunction = ExternalFunctionC func}
    | (identifierContent $ externalFunctionName func) == T.pack "log_dynval" = True
shouldIgnoreInst StoreInst{ storeIsVolatile = True } = True
shouldIgnoreInst inst = False

pairListFind :: (a -> Bool) -> b -> [(a, b)] -> b
pairListFind test def list = foldr check def list
    where check (key, val) _
              | test key = val
          check _ val = val

findSwitchTarget :: BasicBlock -> Word64 -> [(Value, BasicBlock)] -> BasicBlock
findSwitchTarget defaultTarget idx casesList
    = pairListFind test defaultTarget casesList
    where test (ConstantC (ConstantInt{ constantIntValue = int }))
              | int == fromIntegral idx = True
          test (ConstantC (ConstantArray{ constantArrayValues = array }))
              = test $ head array
          test (ConstantC (ConstantVector{ constantVectorValues = vector }))
              = test $ head vector
          test (ConstantC (ConstantAggregateZero{}))
              | idx == 0 = True
          test _ = False

associateInst :: Instruction -> FuncOpContext (Maybe MemlogOp)
associateInst inst
    | shouldIgnoreInst inst = return Nothing
associateInst inst@LoadInst{} = do
    op <- memlogPopErr inst
    case op of
        MemoryOp LoadOp _ -> return $ Just op
        _ -> throwError $ printf "Expected LoadOp; got %s" (show op)
associateInst inst@StoreInst{ storeIsVolatile = False } = do
    op <- memlogPopErr inst
    case op of
        MemoryOp StoreOp _ -> return $ Just op
        _ -> throwError $ printf "Expected StoreOp; got %s" (show op)
associateInst inst@SelectInst{} = liftM Just $ memlogPopErr inst
associateInst inst@BranchInst{} = do
    op <- memlogPopErr inst
    case op of
        BranchOp 0 -> putNextBlock $ branchTrueTarget inst
        BranchOp 1 -> putNextBlock $ branchFalseTarget inst
        _ -> throwError $ printf "Expected branch operation; got %s" (show op)
    return $ Just op
associateInst inst@SwitchInst{ switchDefaultTarget = defaultTarget,
                               switchCases = casesList } = do
    op <- memlogPopErr inst
    case op of
        SwitchOp idx -> putNextBlock $ findSwitchTarget defaultTarget idx casesList
        _ -> throwError "Expected switch operation"
    return $ Just op
associateInst inst@UnconditionalBranchInst{ unconditionalBranchTarget = target } = do
    op <- memlogPopErr inst
    case op of
        BranchOp 0 -> putNextBlock target
        _ -> throwError $ printf "Expected branch operation; got %s" (show op)
    return $ Just op
associateInst inst@CallInst{ callFunction = ExternalFunctionC func,
                             callAttrs = attrs }
    | FANoReturn `elem` externalFunctionAttrs func = skipRest >> return Nothing
    | FANoReturn `elem` attrs = skipRest >> return Nothing
    | T.pack "cpu_loop_exit" == name = skipRest >> return Nothing
    | T.pack "llvm.memset." `T.isPrefixOf` name = do
        op <- memlogPopErr inst
        case op of
            MemoryOp StoreOp addr -> return $ Just $ MemsetOp addr
            _ -> throwError $ printf "Expected store operation (memset)"
    | T.pack "llvm.memcpy." `T.isPrefixOf` name = do
        op1 <- memlogPopErr inst
        op2 <- memlogPopErr inst
        case (op1, op2) of
            (MemoryOp LoadOp src, MemoryOp StoreOp dest) ->
                return $ Just $ MemcpyOp src dest
            _ -> throwError $ printf "Expected load and store operation (memcpy)"
    where name = identifierContent $ externalFunctionName func
associateInst CallInst{ callFunction = FunctionC func } = do
    opStream <- getOpStream
    let (eitherError, memlogState)
            = runState (runErrorT $ associateMemlogWithFunc $ Just func)
                noMemlogState{ memlogOpStream = opStream }
    putOpStream $ memlogOpStream memlogState
    case eitherError of
        Right () -> return ()
        Left err -> throwError err
    let maybeRevMemlog = memlogAssociatedBlocks memlogState
    let revMemlog = fromMaybe (error "no memlog!") maybeRevMemlog
    when (memlogSkipRest memlogState) skipRest
    return $ Just $ HelperFuncOp $ unAppList revMemlog
associateInst RetInst{} = clearNextBlock >> return Nothing
associateInst UnreachableInst{} = do
    skip <- memlogSkipRest <$> get
    throwError $ printf "Unreachable instruction; skipRest = %s" (show skip)
associateInst _ = return Nothing

associateMemlogWithFunc :: Maybe Function -> FuncOpContext ()
associateMemlogWithFunc maybeFunc = do
    func <- case maybeFunc of
        Just func -> return func
        Nothing -> do
            op <- fromMaybe (error "No op to begin block") <$> memlogPopMaybe
            blocks <- memlogAssociatedBlocks <$> get
            tbCount <- case op of
                BeginBlockOp eip tbCount -> return tbCount
                _ -> error $ printf "Expected BeginBlockOp; got %s; previous block %s"
                    (show op) (fromMaybe "none" $ identifierAsString <$> functionName <$>
                        basicBlockFunction <$> fst <$> head <$> suffix 1 <$> blocks)
            blockMap <- memlogBlockMap <$> get
            return $ M.findWithDefault (error $ printf "Couldn't find block with tbCount %d" tbCount)
                tbCount blockMap
    addBlock $ head $ functionBody func
    where addBlock :: BasicBlock -> FuncOpContext ()
          addBlock block = do
              ops <- getOpStream
              associated <- associateBasicBlock block
              appendAssociated (block, associated)
              nextBlock <- memlogNextBlock <$> get
              case nextBlock of
                  Just nextBlock' -> addBlock nextBlock'
                  Nothing -> return ()

associateMemlogWithModule :: Module -> FuncOpContext ()
associateMemlogWithModule mod = forever assocIfRemaining
    where assocIfRemaining = do
              ops <- getOpStream
              unless (null ops) $ associateMemlogWithFunc Nothing

mkBlockMap :: Module -> M.Map Word64 Function
mkBlockMap mod = foldl construct M.empty $ moduleDefinedFunctions mod
    where construct map func = case strippedName func of
              Just suffix -> M.insert
                  (read $ takeWhile C.isDigit suffix) func map
              Nothing -> map
          strippedName func = L.stripPrefix "tcg-llvm-tb-" $
              identifierAsString $ functionName func

associateFuncs :: [MemlogOp] -> Module -> MemlogList
associateFuncs ops mod = unAppList revMemlog
    where revMemlog = fromMaybe (error "No memlog list") maybeRevMemlog
          maybeRevMemlog = memlogAssociatedBlocks $
              execState (associate mod) $ noMemlogState{ memlogOpStream = ops }
          associate funcs = do
              result <- runErrorT $ associateMemlogWithModule mod
              case result of
                  Right associated -> return associated
                  Left err -> error err

showAssociated :: MemlogList -> String
showAssociated theList = L.intercalate "\n\n\n" $ map showBlock theList

showBlock :: (BasicBlock, InstOpList) -> String
showBlock (block, list) = printf "%s: %s:\n%s"
    (show $ functionName $ basicBlockFunction block)
    (show $ basicBlockName block)
    (L.intercalate "\n" $ map showInstOp list)
    where showInstOp (inst, Just op)
              = printf "%s =>\n\t%s" (show inst) (showOp op)
          showInstOp (inst, Nothing) = show inst
          showOp (HelperFuncOp helperMemlog)
              = printf "\n===HELPER===:\n%s\n===END HELPER===" $
                  showAssociated helperMemlog
          showOp op = show op
