module Memlog(MemlogOp(..), AddrOp(..), AddrEntry(..), AddrEntryType(..), AddrFlag(..), parseMemlog, associateFuncs, shouldIgnoreInst, pairListFind, InstOpList, MemlogList, Interesting) where

import Control.Applicative
import Control.Monad(liftM)
import Control.Monad.Trans.State
import Control.Monad.Trans.Class(lift)
import Control.Monad.Trans.Maybe
import Data.Binary.Get(Get, runGet, getWord32host, getWord64host, skip)
import Data.LLVM.Types
import Data.Maybe(isJust, fromMaybe)
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
                HelperFuncOp MemlogList -- For calls out to helper functions
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

parseMemlog :: IO [MemlogOp]
parseMemlog = runGet (many getMemlogEntry) <$> GZ.decompress <$> B.readFile "/tmp/llvm-memlog.log"

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
        -1 -> IrrelevantFlag
        0 -> NoFlag
        1 -> ExceptionFlag
        2 -> ReadlogFlag
        3 -> FuncargFlag
        f -> error ("Parse error on flag " ++ show f)

type InstOpList = [(Instruction, Maybe MemlogOp)]
type MemlogList = [(BasicBlock, InstOpList)]
type MemlogAppList = AppList (BasicBlock, InstOpList)

-- Monads for doing the association.

-- We always keep track of the MemlogOps which are left, in the inner OpContext monad.
type OpContext = State [MemlogOp]
-- Across basic blocks, we keep track of the MemlogOps for each block.
-- The Maybe keeps track of whether we are actually keeping track
-- (i.e. this is during user code, not loading code)
-- The list is kept reversed for efficiency reasons.
type MemlogContext = StateT (Maybe MemlogAppList) OpContext
-- Inside a basic block, watch out to see if we run into a control-flow instruction.
type FuncOpContext = StateT (Maybe BasicBlock) OpContext
memlogPop :: FuncOpContext (Maybe MemlogOp)
memlogPop = do
    stream <- lift get
    case stream of
        op : ops -> lift (put ops) >> return (Just op)
        [] -> return Nothing

memlogPopWithError :: String -> FuncOpContext MemlogOp
memlogPopWithError errMsg = do
    maybeOp <- memlogPop
    case maybeOp of
        Just op -> return op
        Nothing -> error errMsg

memlogPopWithErrorInst :: Instruction -> FuncOpContext MemlogOp
memlogPopWithErrorInst inst = memlogPopWithError $ "Failed on block " ++ (show $ instructionBasicBlock inst)

t x = traceShow x x

associateBasicBlock :: BasicBlock -> FuncOpContext InstOpList
associateBasicBlock block = mapM associateInstWithCopy $ basicBlockInstructions block
    where associateInstWithCopy inst = do
              maybeOp <- associateInst inst
              return (inst, maybeOp)

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
          test _ = False

associateInst :: Instruction -> FuncOpContext (Maybe MemlogOp)
associateInst inst
    | shouldIgnoreInst inst = return Nothing
associateInst inst@LoadInst{} = liftM Just $ memlogPopWithErrorInst inst
associateInst inst@StoreInst{ storeIsVolatile = False }
    = liftM Just $ memlogPopWithErrorInst inst
associateInst inst@SelectInst{} = liftM Just $ memlogPopWithErrorInst inst
associateInst inst@BranchInst{} = do
    op <- memlogPopWithErrorInst inst
    case op of
        BranchOp 0 -> put $ Just $ branchTrueTarget inst
        BranchOp 1 -> put $ Just $ branchFalseTarget inst
        _ -> fail "Expected branch operation"
    return $ Just op
associateInst inst@SwitchInst{ switchDefaultTarget = defaultTarget,
                               switchCases = casesList } = do
    op <- memlogPopWithErrorInst inst
    case op of
        SwitchOp idx -> put $ Just $ findSwitchTarget defaultTarget idx casesList
        _ ->  fail "Expected switch operation"
    return $ Just op
associateInst inst@UnconditionalBranchInst{ unconditionalBranchTarget = target } = do
    put $ Just target
    liftM Just $ memlogPopWithErrorInst inst
associateInst CallInst{ callFunction = FunctionC func } = do
    lift $ do -- inside OpContext
        maybeRevMemlog <- execStateT (associateMemlogWithFunc func) $ Just mkAppList
        let revMemlog = fromMaybe (error "no memlog!") maybeRevMemlog
        return $ Just $ HelperFuncOp $ unAppList revMemlog
associateInst RetInst{} = put Nothing >> return Nothing
associateInst _ = return Nothing

associateMemlogWithFunc :: Function -> MemlogContext ()
associateMemlogWithFunc func = addBlock $ head $ functionBody func
    where addBlock :: BasicBlock -> MemlogContext ()
          addBlock block = do
              ops <- lift get
              (associated, nextBlock) <- lift $ runStateT (associateBasicBlock block) Nothing
              maybeRevMemlogList <- get
              case maybeRevMemlogList of
                  Just revMemlogList -> 
                      put $ Just $ revMemlogList +: (block, associated)
                  _ -> return ()
              case nextBlock of
                  Just nextBlock' -> addBlock nextBlock'
                  Nothing -> return ()

type Interesting = ([Function], [Function], [Function])

associateFuncs :: [MemlogOp] -> Interesting -> MemlogList
associateFuncs ops (before, middle, _) = unAppList revMemlogList
    where revMemlogList = fromMaybe (error "No memlog list") maybeRevMemlogList
          (maybeRevMemlogList, leftoverOps) = runState (beforeM >> middleM) ops
          beforeM = execStateT (mapM_ associateMemlogWithFunc before) Nothing
          middleM = execStateT (mapM_ associateMemlogWithFunc middle) $ Just mkAppList

showAssociated :: MemlogList -> String
showAssociated theList = L.intercalate "\n\n\n" $ map showBlock theList
    where showBlock (block, list) = show (functionName $ basicBlockFunction block) ++ ":" ++ show (basicBlockName block) ++ ":\n" ++ (L.intercalate "\n" $ map showInstOp list)
          showInstOp (inst, maybeOp) = show inst ++ " =>\n\t" ++ showOp maybeOp
          showOp (Just (HelperFuncOp helperMemlog)) = "HELPER: " ++ showAssociated helperMemlog
          showOp maybeOp = show maybeOp
