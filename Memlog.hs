module Memlog(MemlogOp(..), AddrOp(..), AddrEntry(..), AddrEntryType(..), AddrFlag(..), parseMemlog, associateFuncs, MemlogList, Interesting) where

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

import qualified Data.ByteString.Lazy as B
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import Instances
import Pretty

-- Haskell version of C dynamic log structs
data MemlogOp = AddrMemlogOp AddrOp AddrEntry | BranchOp Word32 | SelectOp Bool
    deriving (Eq, Ord, Show)
data AddrOp = LoadOp | StoreOp | BranchAddrOp | SelectAddrOp
    deriving (Eq, Ord, Show, Enum)
data AddrEntry = AddrEntry { addrType :: AddrEntryType
                           , addrVal :: Word64
                           , addrOff :: Word32
                           , addrFlag :: AddrFlag }
    deriving (Eq, Ord, Show)
data AddrEntryType = HAddr | MAddr | IAddr | LAddr | GReg | GSpec | Unk | Const | Ret
    deriving (Eq, Ord, Show, Enum)
data AddrFlag = IrrelevantFlag | NoFlag | ExceptionFlag | ReadlogFlag | FuncargFlag
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
parseMemlog = runGet (many getMemlogEntry) <$> B.readFile "/tmp/llvm-memlog.log"

getMemlogEntry :: Get MemlogOp
getMemlogEntry = do
    entryType <- getWord64host
    out <- case entryType of
        0 -> AddrMemlogOp <$> getAddrOp <*> getAddrEntry
        1 -> BranchOp <$> getWord32host <* skip 28
        2 -> SelectOp <$> getBool <* skip 28
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

type MemlogList = [(BasicBlock, [(Instruction, Maybe MemlogOp)])]

-- Monads for doing the association.

-- We always keep track of the MemlogOps which are left, in the inner OpContext monad.
type OpContext = State [MemlogOp]
-- Across basic blocks, we keep track of the MemlogOps for each block.
-- The Maybe keeps track of whether we are actually keeping track
-- (i.e. this is during user code, not loading code)
-- The list is kept reversed for efficiency reasons.
type MemlogContext = StateT (Maybe MemlogList) OpContext
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

associateBasicBlock :: BasicBlock -> FuncOpContext [(Instruction, Maybe MemlogOp)]
associateBasicBlock = mapM associateInstWithCopy . basicBlockInstructions
    where associateInstWithCopy inst = do
              maybeOp <- associateInst inst
              return (inst, maybeOp)

associateInst :: Instruction -> FuncOpContext (Maybe MemlogOp)
associateInst inst@LoadInst{} = liftM Just $ memlogPopWithErrorInst inst
associateInst inst@StoreInst{ storeIsVolatile = volatile }
    = if volatile
        then return Nothing
        else liftM Just $ memlogPopWithErrorInst inst
associateInst inst@BranchInst{} = do
    op <- memlogPopWithErrorInst inst
    case op of
        BranchOp 0 -> put $ Just $ branchTrueTarget inst
        BranchOp 1 -> put $ Just $ branchFalseTarget inst
        _ -> return ()
    return $ Just op
associateInst inst@UnconditionalBranchInst{ unconditionalBranchTarget = target} = do
    put $ Just target
    liftM Just $ memlogPopWithErrorInst inst
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
                      put $ Just $ (block, associated) : revMemlogList
                  _ -> return ()
              case nextBlock of
                  Just nextBlock' -> addBlock nextBlock'
                  Nothing -> return ()

type Interesting = ([Function], [Function], [Function])

associateFuncs :: [MemlogOp] -> Interesting -> MemlogList
associateFuncs ops (before, middle, _) = reverse revMemlogList
    where revMemlogList = fromMaybe (error "No memlog list") maybeRevMemlogList
          (maybeRevMemlogList, leftoverOps) = runState (beforeM >> middleM) ops
          beforeM = execStateT (mapM_ associateMemlogWithFunc before) Nothing
          middleM = execStateT (mapM_ associateMemlogWithFunc middle) $ Just []

showAssociated :: MemlogList -> String
showAssociated theList = L.intercalate "\n\n" $ map showBlock theList
    where showBlock (block, list) = show (functionName $ basicBlockFunction block) ++ ":\n" ++ (L.intercalate "\n" $ map showInstOp list)
          showInstOp (inst, maybeOp) = show inst ++ " => " ++ show maybeOp
