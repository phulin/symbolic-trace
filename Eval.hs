{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, MultiParamTypeClasses, StandaloneDeriving #-}
-- Symbolic evaluator for basic blocks

module Eval(Symbolic(..), SymbolicState(..), noSymbolicState, runBlocks, messages, messagesByIP, warnings, showWarning, numInstructions) where

import Data.LLVM.Types
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import qualified Data.Set as S
import qualified Data.Bits as Bits
import Data.Word
import Data.Maybe
import Debug.Trace
import Control.Applicative
import Control.Monad
import Control.Monad.State.Lazy
import Control.Monad.Trans.Class(lift, MonadTrans)
import Control.Monad.Trans.Maybe
import Text.Printf(printf)

import Data.RESET.Types
import AppList
import Expr
import Memlog
import Options
import Pretty
import Progress

data LocInfo = LocInfo{
    locExpr :: Expr,
    -- Guest instruction address where loc originated
    locOrigin :: Maybe Word64
} deriving (Eq, Ord, Show)

noLocInfo :: LocInfo
noLocInfo = LocInfo{
    locExpr = IrrelevantExpr,
    locOrigin = Nothing
}

deriving instance (Show a) => Show (Message a)

-- Representation of our [partial] knowledge of machine state.
type Info = M.Map Loc LocInfo
data SymbolicState = SymbolicState {
        symbolicInfo :: Info,
        symbolicPreviousBlock :: Maybe BasicBlock,
        symbolicFunction :: Function,
        -- Map of names for free variables: loads from uninitialized memory
        symbolicVarNameMap :: M.Map (ExprT, AddrEntry) String,
        symbolicCurrentIP :: Maybe Word64,
        symbolicWarnings :: AppList (Maybe Word64, String),
        symbolicMessages :: AppList (Maybe Word64, Message Expr),
        symbolicMessagesByIP :: MS.Map Word64 (AppList (Message Expr)),
        symbolicSkipRest :: Bool,
        symbolicRetVal :: Maybe Expr,
        symbolicTotalInstructions :: Int,
        symbolicInstructionsProcessed :: Int,
        symbolicOptions :: Options
    } deriving Show

messages :: SymbolicState -> [(Maybe Word64, Message Expr)]
messages = unAppList . symbolicMessages

warnings :: SymbolicState -> [(Maybe Word64, String)]
warnings = unAppList . symbolicWarnings

messagesByIP :: Word64 -> SymbolicState -> [Message Expr]
messagesByIP ip SymbolicState{ symbolicMessagesByIP = msgMap }
    = unAppList $ MS.findWithDefault mkAppList ip msgMap

-- Symbolic is our fundamental monad: it holds state about control flow and
-- holds our knowledge of machine state.
type Symbolic = State SymbolicState

class (MonadState SymbolicState m, Functor m) => Symbolicish m where { }
instance (MonadState SymbolicState m, Functor m) => Symbolicish m

-- Atomic operations inside Symbolic.
getInfo :: Symbolicish m => m Info
getInfo = symbolicInfo <$> get
getPreviousBlock :: Symbolicish m => m (Maybe BasicBlock)
getPreviousBlock = symbolicPreviousBlock <$> get
getCurrentFunction :: Symbolicish m => m Function
getCurrentFunction = symbolicFunction <$> get
getCurrentIP :: Symbolicish m => m (Maybe Word64)
getCurrentIP = symbolicCurrentIP <$> get
getSkipRest :: Symbolicish m => m Bool
getSkipRest = symbolicSkipRest <$> get
getRetVal :: Symbolicish m => m (Maybe Expr)
getRetVal = symbolicRetVal <$> get
putInfo :: Symbolicish m => Info -> m ()
putInfo info = modify (\s -> s{ symbolicInfo = info })
putPreviousBlock :: Symbolicish m => Maybe BasicBlock -> m ()
putPreviousBlock block = modify (\s -> s{ symbolicPreviousBlock = block })
putCurrentFunction :: Symbolicish m => Function -> m ()
putCurrentFunction f = modify (\s -> s{ symbolicFunction = f })
putCurrentIP :: Symbolicish m => Maybe Word64 -> m ()
putCurrentIP newIP = modify (\s -> s{ symbolicCurrentIP = newIP })
putRetVal retVal = modify (\s -> s{ symbolicRetVal = retVal })

skipRest :: Symbolicish m => m ()
skipRest = modify (\s -> s{ symbolicSkipRest = True })
clearSkipRest :: Symbolicish m => m ()
clearSkipRest = modify (\s -> s{ symbolicSkipRest = False })

printIP :: Maybe Word64 -> String
printIP (Just realIP) = printf "%x" realIP
printIP Nothing = "unkown"

getStringIP :: Symbolicish m => m String
getStringIP = printIP <$> getCurrentIP

generateName :: Symbolicish m => ExprT -> AddrEntry -> m (Maybe String)
generateName typ addr@AddrEntry{ addrType = MAddr, addrVal = val } = do
    varNameMap <- getVarNameMap
    case M.lookup (typ, addr) varNameMap of
        Just name -> return $ Just name
        Nothing -> do
            let newName = printf "%s_%04x_%d" (pretty typ) (val `rem` (2 ^ 12)) (M.size varNameMap)
            putVarNameMap $ M.insert (typ, addr) newName varNameMap 
            return $ Just newName
    where getVarNameMap = symbolicVarNameMap <$> get
          putVarNameMap m = modify (\s -> s{ symbolicVarNameMap = m })
generateName _ _ = return Nothing

whenM :: Monad m => m Bool -> m () -> m ()
whenM cond action = cond >>= (flip when) action

inUserCode :: Symbolicish m => m Bool
inUserCode = do
    maybeCurrentIP <- getCurrentIP
    return $ case maybeCurrentIP of
        Just currentIP
            | currentIP >= 2 ^ 32 -> False
        _ -> True

message :: Symbolicish m => Message Expr -> m ()
message msg = do
    maybeIP <- getCurrentIP
    modify (\s -> s{ symbolicMessages = symbolicMessages s +: (maybeIP, msg) })
    case maybeIP of
        Just ip -> do
            modify (\s -> s{ 
                symbolicMessagesByIP = MS.alter addMsg ip $ symbolicMessagesByIP s
            })
        Nothing -> return ()
    where addMsg (Just msgs) = Just $ msgs +: msg
          addMsg Nothing = Just $ singleAppList msg

warning :: Symbolicish m => String -> m ()
warning warn = do
    warnings <- symbolicWarnings <$> get
    ip <- getCurrentIP
    modify (\s -> s{ symbolicWarnings = warnings +: (ip, warn) })
    message $ WarningMessage $ showWarning (ip, warn)

showWarning :: (Maybe Word64, String) -> String
showWarning (ip, s) = printf " - (%s) %s" (printIP ip) s

locInfoInsert :: Symbolicish m => Loc -> LocInfo -> m ()
locInfoInsert key locInfo = do
    info <- getInfo
    putInfo $ M.insert key locInfo info
exprFindInfo :: Symbolicish m => Expr -> Loc -> m Expr
exprFindInfo def key = locExpr <$> M.findWithDefault defLocInfo key <$> getInfo
    where defLocInfo = noLocInfo{ locExpr = def }

noSymbolicState :: SymbolicState
noSymbolicState = SymbolicState{
    symbolicInfo = M.empty,
    symbolicPreviousBlock = Nothing,
    symbolicFunction = error "No function.",
    symbolicVarNameMap = M.empty,
    symbolicCurrentIP = Nothing,
    symbolicWarnings = mkAppList,
    symbolicMessages = mkAppList,
    symbolicMessagesByIP = M.empty,
    symbolicSkipRest = False,
    symbolicRetVal = Nothing,
    symbolicTotalInstructions = error "Need total instr count.",
    symbolicInstructionsProcessed = 0,
    symbolicOptions = defaultOptions
}

valueAt :: Symbolicish m => Loc -> m Expr
valueAt loc = exprFindInfo (InputExpr Int64T loc) loc

-- BuildExpr is a monad for building expressions. It allows us to short-
-- circuit the computation and just return IrrelevantExpr, and it also allows
-- us to return detailed errors (for now this is not implemented).
data BuildExprM a
    = Irrelevant
    | ErrorI String
    | JustI a

newtype BuildExprT m a = BuildExprT { runBuildExprT :: m (BuildExprM a) }

type BuildExpr a = BuildExprT (Symbolic) a

-- Monad transformer boilerplate.
instance (Monad m) => Monad (BuildExprT m) where
    x >>= f = BuildExprT $ do
        v <- runBuildExprT x
        case v of
            JustI y -> runBuildExprT (f y)
            Irrelevant -> return Irrelevant
            ErrorI s -> return $ ErrorI s
    return x = BuildExprT (return $ JustI x)
    fail e = BuildExprT (return $ ErrorI e)

instance (Monad m) => Functor (BuildExprT m) where
    fmap f x = x >>= return . f

instance MonadTrans BuildExprT where
    lift m = BuildExprT $ m >>= return . JustI

irrelevant :: (Monad m) => BuildExprT m a
irrelevant = BuildExprT $ return Irrelevant

instance (Monad m) => Applicative (BuildExprT m) where
    pure = return
    (<*>) = ap

instance (Monad m) => Alternative (BuildExprT m) where
    empty = BuildExprT $ return $ ErrorI ""
    mx <|> my = BuildExprT $ do
        x <- runBuildExprT mx
        y <- runBuildExprT my
        case (x, y) of
            (JustI z, _) -> return $ JustI z
            (Irrelevant, _) -> return Irrelevant
            (ErrorI _, JustI z) -> return $ JustI z
            (ErrorI _, Irrelevant) -> return Irrelevant
            (ErrorI s, ErrorI _) -> return $ ErrorI s

instance MonadState SymbolicState (BuildExprT Symbolic) where
    state = lift . state

-- Some conversion functions between different monads
buildExprToMaybeExpr :: (Monad m) => BuildExprT m Expr -> MaybeT m Expr
buildExprToMaybeExpr = MaybeT . liftM buildExprMToMaybeExpr . runBuildExprT

buildExprToMaybeTExpr :: (Monad m, MonadTrans t) => BuildExprT m Expr -> MaybeT (t m) Expr
buildExprToMaybeTExpr = MaybeT . lift . liftM buildExprMToMaybeExpr . runBuildExprT

buildExprMToMaybeExpr :: BuildExprM Expr -> Maybe Expr
buildExprMToMaybeExpr (JustI e) = Just e
buildExprMToMaybeExpr (ErrorI s) = Nothing
buildExprMToMaybeExpr Irrelevant = Just IrrelevantExpr

maybeToM :: (Monad m) => Maybe a -> m a
maybeToM (Just x) = return x
maybeToM (Nothing) = fail ""

identifierToExpr :: Identifier -> BuildExpr Expr
identifierToExpr name = do
    func <- getCurrentFunction
    value <- valueAt (idLoc func name)
    case value of
        IrrelevantExpr -> return IrrelevantExpr -- HACK!!! figure out why this is happening
        e -> return e

valueToExpr :: Value -> BuildExpr Expr
valueToExpr (ConstantC UndefValue{}) = return UndefinedExpr
valueToExpr (ConstantC (ConstantFP _ _ value)) = return $ FLitExpr value 
valueToExpr (ConstantC (ConstantInt _ _ value)) = return $ ILitExpr value
valueToExpr (ConstantC (ConstantValue{ constantInstruction = inst }))
    = foldl1 (<||>) instToExprs inst
valueToExpr (InstructionC inst) = do
    name <- case instructionName inst of
        Just n -> return n
        Nothing -> fail "No name for inst"
    identifierToExpr name
valueToExpr (ArgumentC (Argument{ argumentName = name,
                                  argumentType = argType })) = do
    func <- getCurrentFunction
    identifierToExpr name <|>
        (return $ InputExpr (typeToExprT argType) (idLoc func name))
valueToExpr (GlobalVariableC GlobalVariable{ globalVariableName = name,
                                             globalVariableType = varType }) = do
    func <- getCurrentFunction
    return $ InputExpr (typeToExprT varType) (idLoc func name)
valueToExpr val = warning ("Couldn't find expr for " ++ show val) >> fail ""

lookupValue :: Value -> BuildExpr Expr
lookupValue val = do
    expr <- valueToExpr val
    loc <- case expr of
        InputExpr _ loc' -> return loc'
        _ -> fail ""
    valueAt loc

binaryInstToExprConstructor :: Instruction -> BuildExpr (ExprT -> Expr -> Expr -> Expr)
binaryInstToExprConstructor AddInst{} = return AddExpr
binaryInstToExprConstructor SubInst{} = return SubExpr
binaryInstToExprConstructor MulInst{} = return MulExpr
binaryInstToExprConstructor DivInst{} = return DivExpr
binaryInstToExprConstructor RemInst{} = return RemExpr
binaryInstToExprConstructor ShlInst{} = return ShlExpr
binaryInstToExprConstructor LshrInst{} = return LshrExpr
binaryInstToExprConstructor AshrInst{} = return AshrExpr
binaryInstToExprConstructor AndInst{} = return AndExpr
binaryInstToExprConstructor OrInst{} = return OrExpr
binaryInstToExprConstructor XorInst{} = return XorExpr
binaryInstToExprConstructor _ = fail ""

binaryInstToExpr :: Instruction -> BuildExpr Expr
binaryInstToExpr inst = do
    exprConstructor <- binaryInstToExprConstructor inst
    lhs <- valueToExpr $ binaryLhs inst
    rhs <- valueToExpr $ binaryRhs inst
    return $ exprConstructor (exprTOfInst inst) lhs rhs

castInstToExprConstructor :: Instruction -> BuildExpr (ExprT -> Expr -> Expr)
castInstToExprConstructor TruncInst{} = return TruncExpr
castInstToExprConstructor ZExtInst{} = return ZExtExpr
castInstToExprConstructor SExtInst{} = return SExtExpr
castInstToExprConstructor FPTruncInst{} = return FPTruncExpr
castInstToExprConstructor FPExtInst{} = return FPExtExpr
castInstToExprConstructor FPToSIInst{} = return FPToSIExpr
castInstToExprConstructor FPToUIInst{} = return FPToUIExpr
castInstToExprConstructor SIToFPInst{} = return SIToFPExpr
castInstToExprConstructor UIToFPInst{} = return UIToFPExpr
castInstToExprConstructor PtrToIntInst{} = return PtrToIntExpr
castInstToExprConstructor IntToPtrInst{} = return IntToPtrExpr
castInstToExprConstructor BitcastInst{} = return BitcastExpr
castInstToExprConstructor _ = fail ""

castInstToExpr :: Instruction -> BuildExpr Expr
castInstToExpr inst = do
    exprConstructor <- castInstToExprConstructor inst
    value <- valueToExpr $ castedValue inst
    return $ exprConstructor (exprTOfInst inst) value

-- Decide whether or not to tell the user about a load or a store.
interestingOp :: Expr -> AddrEntry -> Bool
interestingOp _ AddrEntry{ addrFlag = IrrelevantFlag } = False
interestingOp _ AddrEntry{ addrType = GReg, addrVal = reg }
    | reg >= 16 = False
interestingOp _ _ = True

findIncomingValue :: BasicBlock -> [(Value, Value)] -> Value
findIncomingValue prevBlock valList
    = pairListFind test (error err) $ map swap valList
    where err = printf "Couldn't find block in list:\n%s" (show valList)
          swap (a, b) = (b, a)
          test (BasicBlockC block) = block == prevBlock
          test _ = False

typeBytes :: Type -> Integer
typeBytes (TypePointer _ _) = 8
typeBytes (TypeInteger bits) = fromIntegral bits `quot` 8
typeBytes (TypeArray count t) = fromIntegral count * typeBytes t
typeBytes (TypeStruct _ ts _) = sum $ map typeBytes ts
typeBytes t = error $ printf "Unsupported type %s" (show t)

modifyAt :: Int -> a -> [a] -> [a]
modifyAt 0 v (_ : xs) = v : xs
modifyAt n v (x : xs) = x : modifyAt (n - 1) v xs

otherInstToExpr :: Instruction -> BuildExpr Expr
otherInstToExpr PhiNode{ phiIncomingValues = valList } = do
    maybePrevBlock <- getPreviousBlock
    let prevBlock = fromMaybe (error "No previous block!") maybePrevBlock
    valueToExpr $ findIncomingValue prevBlock valList
otherInstToExpr GetElementPtrInst{} = return GEPExpr
otherInstToExpr inst@CallInst{ callFunction = ExternalFunctionC func,
                               callArguments = argValuePairs }
    | externalIsIntrinsic func = do
        args <- mapM valueToExpr $ map fst argValuePairs
        return $ IntrinsicExpr (exprTOfInst inst) func args
otherInstToExpr inst@InsertValueInst{ insertValueAggregate = aggr,
                                      insertValueValue = val,
                                      insertValueIndices = [idx] } = do
    aggrExpr <- valueToExpr aggr
    insertExpr <- valueToExpr val
    let typ = exprTOfInst inst
    case aggrExpr of
        UndefinedExpr -> case typ of
            StructT ts -> return $ StructExpr typ $ modifyAt idx insertExpr $
                replicate (length ts) UndefinedExpr
            _ -> warning "Bad result type!" >> fail ""
        StructExpr t es -> return $ StructExpr t $ modifyAt idx insertExpr es
        _ -> warning (printf "Unrecognized expr at inst '%s'" (show inst)) >> fail ""
otherInstToExpr inst@ExtractValueInst{ extractValueAggregate = aggr,
                                         extractValueIndices = [idx] } = do
    aggrExpr <- valueToExpr aggr
    return $ ExtractExpr (exprTOfInst inst) idx aggrExpr
otherInstToExpr inst@ICmpInst{ cmpPredicate = pred,
                              cmpV1 = val1,
                              cmpV2 = val2 } = do
    expr1 <- valueToExpr val1
    expr2 <- valueToExpr val2
    return $ ICmpExpr pred expr1 expr2
otherInstToExpr _ = fail ""

(<||>) :: Alternative f => (a -> f b) -> (a -> f b) -> a -> f b
(<||>) f1 f2 a = f1 a <|> f2 a

-- List of ways to process instructions and order in which to try them.
-- Each one converts an instruction into the expression which is the
-- instruction's output.
instToExprs :: [Instruction -> BuildExpr Expr]
instToExprs = [ binaryInstToExpr,
                castInstToExpr,
                otherInstToExpr ]

memInstToExpr :: (Instruction, Maybe MemlogOp) -> BuildExpr Expr
memInstToExpr (inst@LoadInst{ loadAddress = addrValue },
                Just (AddrMemlogOp LoadOp addrEntry)) = do
    info <- getInfo
    let typ = exprTOfInst inst
    case addrFlag addrEntry of
        IrrelevantFlag -> return IrrelevantExpr -- Ignore parts of CPU state that Panda doesn't track.
        _ -> do
            expr <- (locExpr <$> maybeToM (M.lookup (MemLoc addrEntry) info)) <|>
                    (LoadExpr typ addrEntry <$> generateName typ addrEntry)
            stringIP <- getStringIP
            origin <-
                (do
                    addrExpr <- valueToExpr addrValue
                    return $ case addrExpr of
                        IntToPtrExpr _ e -> Just e
                        e -> Just e) <|>
                return Nothing
            when (interestingOp expr addrEntry) $
                message $ MemoryMessage LoadOp (pretty addrEntry) expr origin
            return expr
memInstToExpr (inst@SelectInst{ selectTrueValue = trueVal,
                                   selectFalseValue = falseVal },
                  Just (SelectOp selection))
    = valueToExpr $ if selection == 0 then trueVal else falseVal
memInstToExpr _ = fail ""

-- For info updates that might fail, with the intention of no change
-- if the monad comes back Nothing.
type MaybeSymb = MaybeT (Symbolic)

storeUpdate :: (Instruction, Maybe MemlogOp) -> MaybeSymb ()
storeUpdate (inst@StoreInst{ storeIsVolatile = False,
                             storeValue = val,
                             storeAddress = addrValue },
             (Just (AddrMemlogOp StoreOp addr))) = do
    value <- buildExprToMaybeExpr $ valueToExpr val
    currentIP <- getCurrentIP
    origin <-
        (do
            addrExpr <- buildExprToMaybeExpr $ valueToExpr addrValue
            return $ Just $ case addrExpr of
                IntToPtrExpr _ e -> e
                e -> e) <|>
        return Nothing
    when (interestingOp value addr) $
        message $ MemoryMessage StoreOp (pretty addr) value origin
    let locInfo = noLocInfo{ locExpr = value, locOrigin = currentIP }
    locInfoInsert (MemLoc addr) locInfo
-- This will trigger twice with each IP update, but that's okay because the
-- second one is the one we want.
storeUpdate (StoreInst{ storeIsVolatile = True,
                        storeValue = val }, _) = do
    ip <- case valueContent val of
        ConstantC (ConstantInt{ constantIntValue = ipVal }) -> return ipVal
        _ -> warning "Failed to update IP" >> fail ""
    putCurrentIP $ Just $ fromIntegral $ ip
storeUpdate _ = fail ""

exprUpdate :: (Instruction, Maybe MemlogOp) -> MaybeSymb ()
exprUpdate instOp@(inst, _) = do
    id <- maybeToM $ instructionName inst
    func <- getCurrentFunction
    let builtExpr = foldl1 (<||>) instToExprs inst <|> memInstToExpr instOp
    expr <- buildExprToMaybeExpr builtExpr
    currentIP <- getCurrentIP
    let locInfo = noLocInfo{ locExpr = expr, locOrigin = currentIP }
    locInfoInsert (idLoc func id) locInfo

ignoreUpdate :: (Instruction, Maybe MemlogOp) -> MaybeSymb ()
ignoreUpdate (AllocaInst{}, _) = return ()
ignoreUpdate (CallInst{ callFunction = ExternalFunctionC func}, _)
    | (identifierAsString $ externalFunctionName func) == "log_dynval" = return ()
ignoreUpdate _ = fail ""

warnInstOp :: Symbolicish m => (Instruction, Maybe MemlogOp) -> m ()
warnInstOp (inst, op)
    = warning $ printf "Couldn't process inst '%s' with op %s"
        (show inst) (show op)

failedUpdate :: (Instruction, Maybe MemlogOp) -> MaybeSymb ()
failedUpdate instOp = warnInstOp instOp >> fail ""

controlFlowUpdate :: (Instruction, Maybe MemlogOp) -> MaybeSymb ()
controlFlowUpdate (RetInst{ retInstValue = Just val }, _) = do
    expr <- buildExprToMaybeExpr (valueToExpr val)
    putRetVal $ Just expr
controlFlowUpdate (RetInst{}, _) = return ()
controlFlowUpdate (UnconditionalBranchInst{}, _)
    = message UnconditionalBranchMessage
controlFlowUpdate (BranchInst{ branchTrueTarget = trueTarget,
                               branchFalseTarget = falseTarget,
                               branchCondition = cond },
                   Just (BranchOp idx)) = void $ optional $ do
    condExpr <- buildExprToMaybeExpr $ valueToExpr cond
    message $ BranchMessage condExpr (idx == 0)
controlFlowUpdate (SwitchInst{}, _) = return ()
controlFlowUpdate (CallInst{ callFunction = ExternalFunctionC func,
                             callAttrs = attrs }, _)
    | FANoReturn `elem` externalFunctionAttrs func = skipRest
    | FANoReturn `elem` attrs = skipRest
    | "cpu_loop_exit" == identifierAsString (externalFunctionName func)
        = skipRest
controlFlowUpdate (inst@UnreachableInst{}, _) = warning "UNREACHABLE INSTRUCTION!"
controlFlowUpdate _ = fail ""

infoUpdaters :: [(Instruction, Maybe MemlogOp) -> MaybeSymb ()]
infoUpdaters = [ ignoreUpdate,
                 exprUpdate,
                 storeUpdate,
                 controlFlowUpdate,
                 failedUpdate ]

traceInstOp :: (Instruction, Maybe MemlogOp) -> a -> a
traceInstOp (inst, Just (HelperFuncOp _))
    = trace $ printf "%s\n=============\nHELPER FUNCTION:" (show inst)
traceInstOp (inst, Just op) = trace $ printf "%s\n\t\t%s" (show inst) (show op)
traceInstOp (inst, Nothing) = traceShow inst

type ProgressSymb = ProgressT Symbolic
instance MonadState SymbolicState ProgressSymb where
    state = lift . state

helperFuncUpdate :: (Instruction, Maybe MemlogOp) -> MaybeT ProgressSymb ()
helperFuncUpdate (inst@CallInst{ callArguments = argVals,
                                 callFunction = FunctionC func },
                  Just (HelperFuncOp memlog)) = do
    -- Call stack abstraction; store current function so we can restore it later
    currentFunc <- getCurrentFunction
    -- Pass arguments through
    argExprs <- mapM (buildExprToMaybeTExpr . valueToExpr . fst) argVals
    let argNames = map argumentName $ functionParameters func
    let locs = map (idLoc func) argNames
    let argLocInfos = [ noLocInfo{ locExpr = e } | e <- argExprs ]
    zipWithM locInfoInsert locs argLocInfos 
    -- Run and grab return value
    maybeRetVal <- lift $ runBlocks memlog
    -- Understand return value
    optional $ do
        val <- maybeToM $ maybeRetVal
        id <- maybeToM $ instructionName inst
        currentIP <- getCurrentIP
        let locInfo = noLocInfo{ locExpr = val, locOrigin = currentIP }
        locInfoInsert (idLoc currentFunc id) locInfo
    -- Restore old function
    putCurrentFunction currentFunc
helperFuncUpdate _ = fail ""

countInst :: ProgressSymb ()
countInst = do
    insts <- symbolicInstructionsProcessed <$> get
    total <- symbolicTotalInstructions <$> get
    when (insts `rem` (total `quot` 100) == 0) $ 
        progress $ fromIntegral insts / fromIntegral total
    modify (\s -> s{ symbolicInstructionsProcessed = insts + 1 })

updateInfo :: (Instruction, Maybe MemlogOp) -> ProgressSymb ()
updateInfo instOp@(inst, _) = do
    currentIP <- getCurrentIP
    -- when (currentIP == Just 134516607) $ traceInstOp instOp $ return ()
    countInst
    skip <- getSkipRest
    unless skip $ void $ runMaybeT $ helperFuncUpdate instOp <|>
        (liftP $ foldl1 (<||>) infoUpdaters instOp)
    where liftP :: MaybeSymb a -> MaybeT ProgressSymb a
          liftP msx = MaybeT $ ProgressT $ ProgressLift <$> runMaybeT msx

runBlock :: (BasicBlock, InstOpList) -> ProgressSymb (Maybe Expr)
runBlock (block, instOpList) = do
    putCurrentFunction $ basicBlockFunction block 
    putRetVal Nothing
    clearSkipRest
    mapM updateInfo instOpList
    putPreviousBlock $ Just block
    getRetVal

isMemLoc :: Loc -> Bool
isMemLoc MemLoc{} = True
isMemLoc _ = False

numInstructions :: MemlogList -> Int
numInstructions = sum . map (numBlockInstructions . snd)

numBlockInstructions :: InstOpList -> Int
numBlockInstructions ((_, Just (HelperFuncOp memlog)) : xs)
    = 1 + numInstructions memlog + numBlockInstructions xs
numBlockInstructions (x : xs) = 1 + numBlockInstructions xs
numBlockInstructions [] = 0

runBlocks :: MemlogList -> ProgressSymb (Maybe Expr)
runBlocks blocks = do
    retVals <- mapM runBlock blocks
    return $ last retVals

showInfo :: Info -> String
showInfo = unlines . map showEach . filter doShow . M.toList
    where showEach (key, val) = printf "%s %s-> %s" (pretty key) origin (show (locExpr val))
              where origin = fromMaybe "" $ printf "(from %x) " <$> locOrigin val
          doShow (IdLoc{}, LocInfo{ locExpr = expr }) = doShowExpr expr
          doShow (MemLoc{}, LocInfo{ locExpr = IrrelevantExpr }) = False
          doShow _ = True
          doShowExpr IrrelevantExpr = False
          doShowExpr ILitExpr{} = False
          doShowExpr LoadExpr{} = False
          doShowExpr InputExpr{} = True
          doShowExpr expr = True
