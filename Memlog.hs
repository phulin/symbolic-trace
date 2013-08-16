{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
module Memlog(MemlogOp(..), AddrOp(..), AddrEntry(..), AddrEntryType(..), AddrFlag(..), parseMemlog, associateFuncs, shouldIgnoreInst, pairListFind, InstOpList, MemlogList, Interesting) where

import Control.Applicative
import Control.Monad(liftM)
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Trans(lift)
import Control.Monad.Trans.Maybe
import Data.Binary.Get(Get, runGet, getWord32host, getWord64host, skip)
import Data.LLVM.Types
import Data.Maybe(isJust, fromMaybe, catMaybes)
import Data.Word(Word32, Word64)
import Text.Printf(printf)
import Debug.Trace

import qualified Codec.Compression.GZip as GZ
import qualified Data.ByteString.Lazy as B
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import Data.RESET.Types
import AppList
import Instances
import Pretty

-- Haskell version of C dynamic log structs
data MemlogOp = AddrMemlogOp AddrOp AddrEntry |
                BranchOp Word32 |
                SelectOp Word32 |
                SwitchOp Word32 | 
                ExceptionOp |
                HelperFuncOp MemlogList | -- For calls out to helper functions
                MemsetOp AddrEntry |
                MemcpyOp AddrEntry AddrEntry
    deriving (Eq, Ord, Show)

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
parseMemlog file = runGet (many getMemlogEntry) <$> GZ.decompress <$> B.readFile file

getMemlogEntry :: Get MemlogOp
getMemlogEntry = do
    entryType <- getWord64host
    out <- case entryType of
        0 -> AddrMemlogOp <$> getAddrOp <*> getAddrEntry
        1 -> BranchOp <$> getWord32host <* skip 28
        2 -> SelectOp <$> getWord32host <* skip 28
        3 -> SwitchOp <$> getWord32host <* skip 28
        4 -> ExceptionOp <$ skip 28
        _ -> error "Unknown entry type"
    return out

getBool :: Get Bool
getBool = do
    word32 <- getWord32host
    return $ case word32 of
        0 -> False
        _ -> True

getAddrOp :: Get AddrOp
getAddrOp = (toEnum . fromIntegral) <$> getWord64host

getAddrEntry :: Get AddrEntry
getAddrEntry = AddrEntry <$> ((toEnum . fromIntegral) <$> getWord64host) <*> getWord64host <*> getWord32host <*> getAddrFlag

getAddrFlag :: Get AddrFlag
getAddrFlag = do
    addrFlagType <- getWord32host
    return $ case addrFlagType of
        5 -> IrrelevantFlag
        0 -> NoFlag
        1 -> ExceptionFlag
        2 -> ReadlogFlag
        3 -> FuncargFlag
        f -> error ("Parse error in dynamic log: Unexpected flag " ++ show f)

type InstOpList = [(Instruction, Maybe MemlogOp)]
type MemlogList = [(BasicBlock, InstOpList)]
type MemlogAppList = AppList (BasicBlock, InstOpList)

-- Monads for doing the association.

data MemlogState = MemlogState{
    -- Work already done in current block. We use this instead of a mapM so we
    -- can do better error reporting.
    memlogCurrentAssociated :: AppList (Instruction, Maybe MemlogOp),
    -- Already associated blocks. If the Maybe is Nothing, we don't keep track
    -- (i.e. this is loading code, not something we're actually interested in)
    memlogAssociatedBlocks :: Maybe MemlogAppList,
    memlogNextBlock :: Maybe BasicBlock, -- Next block to process
    memlogSkipRest :: Bool
}

noMemlogState :: MemlogState
noMemlogState = MemlogState{
    memlogCurrentAssociated = mkAppList,
    memlogAssociatedBlocks = Just mkAppList,
    memlogNextBlock = Nothing,
    memlogSkipRest = False
}

class (Functor m, Monad m, MonadState MemlogState m) => Memlogish m where
instance (Functor m, Monad m, MonadState MemlogState m) => Memlogish m

class (Functor m, Monad m) => OpStream m where
    getOpStream :: m [MemlogOp]
    putOpStream :: [MemlogOp] -> m ()

type OpContext = State [MemlogOp]
type MemlogContext = StateT MemlogState OpContext
type FuncOpContext = ErrorT String MemlogContext

instance OpStream OpContext where
    getOpStream = get
    putOpStream = put

instance OpStream MemlogContext where
    getOpStream = lift getOpStream
    putOpStream = lift . putOpStream

instance OpStream FuncOpContext where
    getOpStream = lift getOpStream
    putOpStream = lift . putOpStream

memlogPopMaybe :: OpStream m => m (Maybe MemlogOp)
memlogPopMaybe = do
    stream <- getOpStream
    case stream of
        op : ops -> putOpStream ops >> return (Just op)
        [] -> return Nothing

memlogPopErr :: OpStream m => Instruction -> m MemlogOp
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
    | (identifierAsString $ externalFunctionName func) == "log_dynval" = True
shouldIgnoreInst StoreInst{ storeIsVolatile = True } = True
shouldIgnoreInst inst = False

pairListFind :: (a -> Bool) -> b -> [(a, b)] -> b
pairListFind test def list = foldr check def list
    where check (key, val) _
              | test key = val
          check _ val = val

findSwitchTarget :: BasicBlock -> Word32 -> [(Value, BasicBlock)] -> BasicBlock
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
        AddrMemlogOp LoadOp _ -> return $ Just op
        _ -> throwError $ printf "Expected LoadOp; got %s" (show op)
associateInst inst@StoreInst{ storeIsVolatile = False } = do
    op <- memlogPopErr inst
    case op of
        AddrMemlogOp StoreOp _ -> return $ Just op
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
    | "cpu_loop_exit" == name = skipRest >> return Nothing
    | "llvm.memset." `L.isPrefixOf` name = do
        op <- memlogPopErr inst
        case op of
            AddrMemlogOp StoreOp addr -> return $ Just $ MemsetOp addr
            _ -> throwError $ printf "Expected store operation (memset)"
    | "llvm.memcpy." `L.isPrefixOf` name = do
        op1 <- memlogPopErr inst
        op2 <- memlogPopErr inst
        case (op1, op2) of
            (AddrMemlogOp LoadOp src, AddrMemlogOp StoreOp dest) ->
                return $ Just $ MemcpyOp src dest
            _ -> throwError $ printf "Expected load and store operation (memcpy)"
    where name = identifierAsString $ externalFunctionName func
associateInst CallInst{ callFunction = FunctionC func } = do
    (eitherError, memlogState) <- lift $ lift $
        runStateT (runErrorT $ associateMemlogWithFunc func) noMemlogState
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

associateMemlogWithFunc :: Function -> FuncOpContext ()
associateMemlogWithFunc func = addBlock $ head $ functionBody func
    where addBlock :: BasicBlock -> FuncOpContext ()
          addBlock block = do
              ops <- lift get
              associated <- associateBasicBlock block
              appendAssociated (block, associated)
              nextBlock <- memlogNextBlock <$> get
              case nextBlock of
                  Just nextBlock' -> addBlock nextBlock'
                  Nothing -> return ()

type Interesting = ([Function], [Function], [Function])

associateFuncs :: [MemlogOp] -> Interesting -> MemlogList
associateFuncs ops (before, middle, _) = unAppList revMemlog
    where revMemlog = fromMaybe (error "No memlog list") maybeRevMemlog
          maybeRevMemlog = memlogAssociatedBlocks $ evalState (beforeM >> middleM) ops
          beforeM = execStateT (associate before) noMemlogState
          middleM = execStateT (associate middle) noMemlogState
          associate funcs = do
              result <- runErrorT $ mapM_ associateMemlogWithFunc funcs
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
