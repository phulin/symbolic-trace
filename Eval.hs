-- Symbolic evaluator for basic blocks

module Main where

import Data.LLVM.Types
import LLVM.Parse
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Bits as Bits
import Data.Word
import Control.Applicative
import Data.Maybe
import Debug.Trace
import Control.Monad
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Class(lift, MonadTrans)
import Control.Monad.Trans.Maybe
import Text.Printf(printf)

import Expr
import Memlog
import Pretty

data LocInfo = LocInfo{
    locExpr :: Expr,
    locRelevant :: Bool,
    -- Guest instruction address where loc originated
    locOrigin :: Maybe Word64
} deriving (Eq, Ord, Show)

noLocInfo :: LocInfo
noLocInfo = LocInfo{
    locExpr = IrrelevantExpr,
    locRelevant = False,
    locOrigin = Nothing
}

-- Representation of our [partial] knowledge of machine state.
type Info = M.Map Loc LocInfo
data SymbolicState = SymbolicState {
        symbolicInfo :: Info,
        symbolicNextBlock :: Maybe BasicBlock,
        symbolicFunction :: Function,
        -- Map of names for free variables: loads from uninitialized memory
        symbolicVarNameMap :: M.Map (ExprT, AddrEntry) String,
        symbolicCurrentIP :: Maybe Word64,
        symbolicWarnings :: [String]
    } deriving (Eq, Ord, Show)
-- Symbolic is our fundamental monad: it holds state about control flow and
-- holds our knowledge of machine state.
type Symbolic = State SymbolicState

-- Atomic operations inside Symbolic.
getInfo :: Symbolic Info
getInfo = symbolicInfo <$> get
getNextBlock :: Symbolic (Maybe BasicBlock)
getNextBlock = symbolicNextBlock <$> get
getCurrentFunction :: Symbolic Function
getCurrentFunction = symbolicFunction <$> get
getCurrentIP :: Symbolic (Maybe Word64)
getCurrentIP = symbolicCurrentIP <$> get
putInfo :: Info -> Symbolic ()
putInfo info = modify (\s -> s{ symbolicInfo = info })
putNextBlock :: Maybe BasicBlock -> Symbolic ()
putNextBlock maybeBlock = modify (\s -> s{ symbolicNextBlock = maybeBlock })
putCurrentFunction :: Function -> Symbolic ()
putCurrentFunction f = modify (\s -> s{ symbolicFunction = f })
putCurrentIP :: Maybe Word64 -> Symbolic ()
putCurrentIP newIP = modify (\s -> s{ symbolicCurrentIP = newIP })

generateName :: ExprT -> AddrEntry -> Symbolic (Maybe String)
generateName typ addr@AddrEntry{ addrType = MAddr, addrVal = val } = do
    varNameMap <- getVarNameMap
    case M.lookup (typ, addr) varNameMap of
        Just name -> return $ Just name
        Nothing -> do
            let newName = printf "%s_%03x_%d" (pretty typ) (val `rem` (2 ^ 12)) (M.size varNameMap)
            putVarNameMap $ M.insert (typ, addr) newName varNameMap 
            return $ Just newName
    where getVarNameMap = symbolicVarNameMap <$> get
          putVarNameMap m = modify (\s -> s{ symbolicVarNameMap = m })
generateName _ _ = return Nothing

warning :: String -> Symbolic ()
warning warn = do
    warnings <- symbolicWarnings <$> get
    modify (\s -> s{ symbolicWarnings = warnings ++ [warn] })

locInfoInsert :: Loc -> LocInfo -> Symbolic ()
locInfoInsert key locInfo = do
    info <- getInfo
    putInfo $ M.insert key locInfo info
makeRelevant :: Loc -> Symbolic ()
makeRelevant loc = do
    info <- getInfo
    putInfo $ M.adjust (\li -> li{ locRelevant = True }) loc info
exprFindInfo :: Expr -> Loc -> Symbolic Expr
exprFindInfo def key = locExpr <$> M.findWithDefault defLocInfo key <$> getInfo
    where defLocInfo = noLocInfo{ locExpr = def }
isRelevant :: Loc -> Symbolic Bool
isRelevant loc = do
    info <- getInfo
    case M.lookup loc info of
        Nothing -> return False
        Just locInfo -> return $ locRelevant locInfo

noSymbolicState :: SymbolicState
noSymbolicState = SymbolicState{ symbolicInfo = M.empty,
                                 symbolicNextBlock = Nothing,
                                 symbolicFunction = error "No function.",
                                 symbolicVarNameMap = M.empty,
                                 symbolicCurrentIP = Nothing,
                                 symbolicWarnings = [] }

valueAt :: Loc -> Symbolic Expr
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

instance MonadTrans BuildExprT where
    lift m = BuildExprT $ do
        x <- m
        return $ JustI x

irrelevant :: (Monad m) => BuildExprT m a
irrelevant = BuildExprT $ return Irrelevant

instance (Monad m) => Functor (BuildExprT m) where
    fmap f x = x >>= return . f

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

-- Some conversion functions between different monads
buildExprToMaybeExpr :: (Functor m, Monad m) => BuildExprT m Expr -> MaybeT m Expr
buildExprToMaybeExpr = MaybeT . fmap buildExprMToMaybeExpr . runBuildExprT

buildExprMToMaybeExpr :: BuildExprM Expr -> Maybe Expr
buildExprMToMaybeExpr (JustI e) = Just e
buildExprMToMaybeExpr (ErrorI s) = Nothing
buildExprMToMaybeExpr Irrelevant = Just IrrelevantExpr

maybeToM :: (Monad m) => Maybe a -> m a
maybeToM (Just x) = return x
maybeToM (Nothing) = fail ""

instructionToExpr :: Instruction -> BuildExpr Expr
instructionToExpr inst = do
    name <- case instructionName inst of
        Just n -> return n
        Nothing -> fail "No name for inst"
    func <- lift getCurrentFunction
    value <- lift $ valueAt (IdLoc func name)
    case value of
        IrrelevantExpr -> irrelevant
        e -> return e

valueContentToExpr :: ValueContent -> BuildExpr Expr
valueContentToExpr (ConstantC (ConstantFP _ _ value)) = return $ FLitExpr value 
valueContentToExpr (ConstantC (ConstantInt _ _ value)) = return $ ILitExpr value
valueContentToExpr (ConstantC (ConstantValue{ constantInstruction = inst })) = instructionToExpr inst
valueContentToExpr (InstructionC inst) = instructionToExpr inst
valueContentToExpr (ArgumentC (Argument{ argumentName = name,
                                         argumentType = argType })) = do
    func <- lift getCurrentFunction
    return $ InputExpr (typeToExprT argType) (IdLoc func name)
valueContentToExpr val = lift (warning ("Couldn't find expr for " ++ show val)) >> fail ""

valueToExpr :: Value -> BuildExpr Expr
valueToExpr = valueContentToExpr . valueContent

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

loadInstToExpr :: (Instruction, Maybe MemlogOp) -> BuildExpr Expr
loadInstToExpr (inst@LoadInst{ loadAddress = addr },
                Just (AddrMemlogOp LoadOp addrEntry)) = do
    info <- lift getInfo
    let typ = exprTOfInst inst
    case addrFlag addrEntry of
        IrrelevantFlag -> irrelevant -- Ignore parts of CPU state that Panda doesn't track.
        _ -> (locExpr <$> maybeToM (M.lookup (MemLoc addrEntry) info)) <|>
             (LoadExpr typ addrEntry <$> (lift $ generateName typ addrEntry))
loadInstToExpr _ = fail ""

gepInstToExpr :: Instruction -> BuildExpr Expr
gepInstToExpr inst@GetElementPtrInst{ _instructionType = instType,
                                      getElementPtrValue = value,
                                      getElementPtrIndices = indices } = do
    valueExpr <- valueToExpr value
    size <- case instType of
        TypePointer (TypeInteger bits) _ -> return $ bits `quot` 8
        other -> lift (warning ("Type failure: " ++ show other)) >> fail ""
    index <- case map valueContent indices of
        [ConstantC (ConstantInt{ constantIntValue = idx })] -> return idx
        other -> lift (warning ("Value failure: " ++ show other)) >> fail ""
    return $ IntToPtrExpr PtrT $ AddExpr (exprTOfInst inst) valueExpr (ILitExpr $ fromIntegral size * index)
gepInstToExpr _ = fail ""

helperInstToExpr :: Instruction -> BuildExpr Expr
helperInstToExpr inst@CallInst{ callFunction = funcValue,
                                callArguments = funcArgs } = do
    case valueContent funcValue of
        ExternalFunctionC (ExternalFunction{ externalFunctionType = funcType,
                                             externalFunctionName = funcId }) ->
            if "helper_" `L.isPrefixOf` identifierAsString funcId
                then case funcArgs of
                    [] -> lift (warning (printf "Stateful helper %s" (show funcId))) >> fail ""
                    [(argVal, _)] -> do
                        argExpr <- valueToExpr argVal
                        return $ CastHelperExpr (exprTOfInst inst) funcId argExpr
                    [(argVal1, _), (argVal2, _)] -> do
                        case funcType of
                            TypeFunction TypeVoid _ _ ->
                                lift $ warning $ printf "Stateful binary helper %s" (show funcId)
                            _ -> return ()
                        argExpr1 <- valueToExpr argVal1
                        argExpr2 <- valueToExpr argVal2
                        return $ BinaryHelperExpr (exprTOfInst inst) funcId argExpr1 argExpr2
                    _ -> lift (warning (printf "Bad funcArgs: %s(%s)" (show funcId) (show funcArgs))) >> fail ""
                else fail ""
        _ -> fail ""
helperInstToExpr _ = fail ""

icmpInstToExpr :: Instruction -> BuildExpr Expr
icmpInstToExpr inst@ICmpInst{ cmpPredicate = pred,
                              cmpV1 = val1,
                              cmpV2 = val2 } = do
    expr1 <- valueToExpr val1
    expr2 <- valueToExpr val2
    return $ ICmpExpr pred (simplify expr1) (simplify expr2)
icmpInstToExpr _ = fail ""

traceInst :: Instruction -> a -> a
traceInst inst = trace ("Couldn't process inst " ++ (show inst))

t :: (Show a) => a -> a
t x = traceShow x x

maybeTraceInst :: Instruction -> a -> a
maybeTraceInst inst@CallInst{} = case valueContent $ callFunction inst of
    ExternalFunctionC func
        | (identifierAsString $ externalFunctionName func) == "log_dynval" -> id
        | otherwise -> traceInst inst
    _ -> traceInst inst
maybeTraceInst inst@StoreInst{ storeIsVolatile = True } = id
maybeTraceInst inst = traceInst inst

(<||>) :: Alternative f => (a -> f b) -> (a -> f b) -> a -> f b
(<||>) f1 f2 a = f1 a <|> f2 a

-- List of ways to process instructions and order in which to try them.
instToExprs :: [Instruction -> BuildExpr Expr]
instToExprs = [ binaryInstToExpr,
                castInstToExpr,
                gepInstToExpr,
                helperInstToExpr,
                icmpInstToExpr ]

memInstToExprs :: [(Instruction, Maybe MemlogOp) -> BuildExpr Expr]
memInstToExprs = [ loadInstToExpr ]

-- For info updates that might fail, with the intention of no change
-- if the monad comes back Nothing.
type MaybeSymb = MaybeT (Symbolic)

makeValueContentRelevant :: ValueContent -> Symbolic ()
makeValueContentRelevant (InstructionC inst) = do
    func <- getCurrentFunction
    case instructionName inst of
        Just id -> makeRelevant $ IdLoc func id
        _ -> return ()
makeValueContentRelevant _ = return ()

makeValueRelevant :: Value -> Symbolic ()
makeValueRelevant = makeValueContentRelevant . valueContent

storeUpdate :: (Instruction, Maybe MemlogOp) -> MaybeSymb ()
storeUpdate (inst@StoreInst{ storeIsVolatile = False,
                                  storeValue = val },
                  Just (AddrMemlogOp StoreOp addr)) = do
    value <- buildExprToMaybeExpr $ valueToExpr val
--     if usesEsp value && not (addrFlag addr == IrrelevantFlag) then return ()
--         else trace ("STORE: " ++ show value ++ " ===> " ++ pretty addr) $ return ()
    currentIP <- lift getCurrentIP
    let locInfo = noLocInfo{ locExpr = value, locOrigin = currentIP }
    lift $ locInfoInsert (MemLoc addr) locInfo
    lift $ makeRelevant $ MemLoc addr
    lift $ makeValueRelevant val
-- This will trigger twice with each IP update, but that's okay because the
-- second one is the one we want.
storeUpdate (StoreInst{ storeIsVolatile = True,
                        storeValue = val }, _) = do
    ip <- case valueContent val of
        ConstantC (ConstantInt{ constantIntValue = ipVal }) -> return ipVal
        _ -> lift (warning "Failed to update IP") >> fail ""
    lift $ putCurrentIP $ Just $ fromIntegral $ ip
storeUpdate _ = fail ""

exprUpdate :: (Instruction, Maybe MemlogOp) -> MaybeSymb ()
exprUpdate instOp@(inst, _) = do
    id <- maybeToM $ instructionName inst
    func <- lift getCurrentFunction
    let builtExpr = (foldl1 (<||>) instToExprs) inst <|>
                     loadInstToExpr instOp
    expr <- buildExprToMaybeExpr builtExpr
--     case expr of
--         IrrelevantExpr -> return ()
--         _ -> if not $ usesEsp expr
--             then traceShow (id, expr) $ return ()
--             else return ()
    currentIP <- lift getCurrentIP
    let simplified = repeatf 8 simplify expr
    let locInfo = noLocInfo{ locExpr = simplified, locOrigin = currentIP }
    lift $ locInfoInsert (IdLoc func id) locInfo
    where repeatf 0 f x = trace "repeatf overflow, bailing" x
          repeatf n f x
              | x == f x = x
              | otherwise = repeatf (n - 1) f $ f x 

-- Ignore alloca instructions
nullUpdate :: (Instruction, Maybe MemlogOp) -> MaybeSymb ()
nullUpdate (AllocaInst{}, _) = return ()
nullUpdate _ = fail ""

controlFlowUpdate :: (Instruction, Maybe MemlogOp) -> MaybeSymb ()
controlFlowUpdate (RetInst{ retInstValue = Just val }, _) = do
    lift $ makeValueRelevant val
    lift $ putNextBlock $ Nothing
controlFlowUpdate (UnconditionalBranchInst{ unconditionalBranchTarget = target }, _)
    = lift $ putNextBlock $ Just target
controlFlowUpdate inst@(BranchInst{ branchTrueTarget = trueTarget,
                                    branchFalseTarget = falseTarget,
                                    branchCondition = cond },
                        Just (BranchOp idx)) = do
--     trace ("BRANCH: " ++ show cond ++ "\n    " ++ show inst) $ return ()
    lift $ makeValueRelevant $ cond
    case idx of
        0 -> lift $ putNextBlock $ Just trueTarget
        1 -> lift $ putNextBlock $ Just falseTarget
        _ -> error "Invalid branch index"
controlFlowUpdate _ = fail ""

infoUpdaters :: [(Instruction, Maybe MemlogOp) -> MaybeSymb ()]
infoUpdaters = [ exprUpdate, storeUpdate, controlFlowUpdate, nullUpdate ]

updateInfo :: (Instruction, Maybe MemlogOp) -> Symbolic ()
updateInfo instOp@(inst, _) = void $ runMaybeT $ foldl1 (<||>) infoUpdaters instOp

runBlock :: MemlogMap -> BasicBlock -> Symbolic ()
runBlock memlogMap block = do
    mapM updateInfo instOpList
    nextBlock <- getNextBlock
    case nextBlock of
        Just block -> runBlock memlogMap block
        Nothing -> return ()
    where instOpList = M.findWithDefault (error $ "Couldn't find basic block instruction list for " ++ show (functionName $ basicBlockFunction block) ++ show (basicBlockName block)) block memlogMap

isMemLoc :: Loc -> Bool
isMemLoc MemLoc{} = True
isMemLoc _ = False

-- Run a single LLVM function - equivalently, a basic block in the guest code.
runFunction :: MemlogMap -> Function -> Symbolic ()
-- runFunction memlogMap initialInfo f = initialInfo `seq` trace ("\n\n" ++ show (functionName f)) $ symbolicInfo state
runFunction memlogMap f = do
    putCurrentFunction f
    runBlock memlogMap $ head $ functionBody f

runFunctions :: MemlogMap -> [Function] -> (Info, [String])
runFunctions memlogMap fs = (symbolicInfo state, symbolicWarnings state)
    where computation = mapM_ (runFunction memlogMap) fs
          state = execState computation initialState
          initialState = noSymbolicState{ symbolicFunction = head fs }

usesEsp :: Expr -> Bool
usesEsp = foldExpr folders
    where falseFolders = constFolders False
          isLoadEsp _ addr _ = pretty addr == "ESP"
          folders = falseFolders{
              --iLitFolder = const True,
              --fLitFolder = const True,
              loadFolder = isLoadEsp,
              binaryCombiner = (||)
          }

showInfo :: Info -> String
showInfo = unlines . map showEach . filter doShow . M.toList
    where showEach (key, val) = printf "%s %s-> %s" (pretty key) origin (show (locExpr val))
              where origin = fromMaybe "" $ printf "(from %x) " <$> locOrigin val
          doShow (_, LocInfo{ locRelevant = False }) = False
          doShow (IdLoc{}, LocInfo{ locExpr = expr }) = doShowExpr expr
          doShow (MemLoc{}, LocInfo{ locExpr = IrrelevantExpr }) = False
          doShow _ = True
          doShowExpr IrrelevantExpr = False
          doShowExpr ILitExpr{} = False
          doShowExpr LoadExpr{} = False
          doShowExpr InputExpr{} = False
          doShowExpr expr = not $ usesEsp expr

interesting :: [String] -> [String]
interesting fs = L.dropWhileEnd boring $ dropWhile boring fs
    where boring = not . L.isInfixOf "main"

main :: IO ()
main = do
    (Right theMod) <- parseLLVMFile defaultParserOptions "/tmp/llvm-mod.bc"
    funcNameList <- lines <$> readFile "/tmp/llvm-functions.log"
    let mainName = head $ filter (L.isInfixOf "main") funcNameList
    let findFunc name = fromMaybe (error $ "Couldn't find function " ++ name) $ findFunctionByName theMod name
    let funcList = map findFunc funcNameList
    let interestingNames = interesting funcNameList
    let interestingNameSet = S.fromList interestingNames
    let interestingFuncs = map findFunc interestingNames
    memlog <- parseMemlog
    let associated = associateFuncs memlog interestingNameSet funcList
    -- putStrLn $ showAssociated associated
    let (info, warnings) = runFunctions associated interestingFuncs
    putStrLn "Warnings:"
    putStr " - "
    putStrLn $ L.intercalate "\n - " warnings
    putStrLn ""
    putStrLn $ showInfo $ info
