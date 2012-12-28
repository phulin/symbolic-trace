-- Symbolic evaluator for basic blocks

module Main where

import Data.LLVM.Types
import LLVM.Parse
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Bits as Bits
import Data.Word
import Control.Applicative
import Data.Maybe
import Debug.Trace
-- import Text.Parsec(Parsec, endBy, string)
-- import Text.Parsec.String(parseFromFile)
-- import Text.Parsec.Extra(integer, eol)
import Data.Binary.Get(Get, runGet, getWord32host, getWord64host, skip)
import qualified Data.ByteString.Lazy as B
import Control.Monad
import Control.Monad.State.Lazy
import Control.Monad.Trans.Class(lift)
import Text.Printf(printf)

type UInt = Word64

data Loc = IdLoc Identifier | MemLoc AddrEntry
    deriving (Eq, Ord, Show)
data ExprT = VoidT | PtrT | Int8T | Int32T | Int64T | FloatT | DoubleT
    deriving (Eq, Ord, Show)
data Expr =
    AddExpr ExprT Expr Expr |
    SubExpr ExprT Expr Expr |
    MulExpr ExprT Expr Expr |
    DivExpr ExprT Expr Expr |
    RemExpr ExprT Expr Expr |
    ShlExpr ExprT Expr Expr |
    LshrExpr ExprT Expr Expr |
    AshrExpr ExprT Expr Expr |
    AndExpr ExprT Expr Expr |
    OrExpr ExprT Expr Expr |
    XorExpr ExprT Expr Expr |
    TruncExpr ExprT Expr |
    ZExtExpr ExprT Expr |
    SExtExpr ExprT Expr |
    FPTruncExpr ExprT Expr |
    FPExtExpr ExprT Expr |
    FPToSIExpr ExprT Expr |
    FPToUIExpr ExprT Expr |
    SIToFPExpr ExprT Expr |
    UIToFPExpr ExprT Expr |
    PtrToIntExpr ExprT Expr |
    IntToPtrExpr ExprT Expr |
    BitcastExpr ExprT Expr |
    LoadExpr ExprT AddrEntry |
    BinaryHelperExpr ExprT Identifier Expr Expr | -- not witnessed
    CastHelperExpr ExprT Identifier Expr |
    ILitExpr Integer | -- takes any integer type
    FLitExpr Double | -- takes any float type
    InputExpr ExprT Loc |
    IrrelevantExpr
    deriving (Eq, Ord)

instance Show Expr where
    show (AddExpr _ e1 e2) = printf "(%s + %s)" (show e1) (show e2)
    show (SubExpr _ e1 e2) = printf "(%s - %s)" (show e1) (show e2)
    show (MulExpr _ e1 e2) = printf "(%s * %s)" (show e1) (show e2)
    show (DivExpr _ e1 e2) = printf "(%s / %s)" (show e1) (show e2)
    show (RemExpr _ e1 e2) = printf "(%s % %s)" (show e1) (show e2)
    show (ShlExpr _ e1 e2) = printf "(%s << %s)" (show e1) (show e2)
    show (LshrExpr _ e1 e2) = printf "(%s L>> %s)" (show e1) (show e2)
    show (AshrExpr _ e1 e2) = printf "(%s A>> %s)" (show e1) (show e2)
    show (AndExpr _ e1 e2) = printf "(%s & %s)" (show e1) (show e2)
    show (OrExpr _ e1 e2) = printf "(%s | %s)" (show e1) (show e2)
    show (XorExpr _ e1 e2) = printf "(%s ^ %s)" (show e1) (show e2)
    show (TruncExpr _ e) = printf "Trunc(%s)" (show e)
    show (ZExtExpr _ e) = printf "ZExt(%s)" (show e)
    show (SExtExpr _ e) = printf "SExt(%s)" (show e)
    show (FPTruncExpr _ e) = printf "FPTrunc(%s)" (show e)
    show (FPExtExpr _ e) = printf "FPExt(%s)" (show e)
    show (FPToSIExpr _ e) = printf "FPToSI(%s)" (show e)
    show (FPToUIExpr _ e) = printf "FPToUI(%s)" (show e)
    show (SIToFPExpr _ e) = printf "SIToFP(%s)" (show e)
    show (UIToFPExpr _ e) = printf "UIToFP(%s)" (show e)
    show (PtrToIntExpr _ e) = printf "PtrToInt(%s)" (show e)
    show (IntToPtrExpr _ e) = printf "IntToPtr(%s)" (show e)
    show (BitcastExpr _ e) = printf "Bitcast(%s)" (show e)
    show (LoadExpr _ AddrEntry{ addrType = GReg, addrVal = reg }) = case reg of
        0 -> "EAX"
        1 -> "ECX"
        2 -> "EDX"
        3 -> "EBX"
        4 -> "ESP"
        5 -> "EBP"
        6 -> "ESI"
        7 -> "EDI"
        _ -> "Reg" ++ show reg
    show (LoadExpr _ addr) = printf "*%s" (show addr)
    show (BinaryHelperExpr _ id e1 e2) = printf "%s(%s, %s)" (show id) (show e1) (show e2)
    show (CastHelperExpr _ id e) = printf "%s(%s)" (show id) (show e)
    show (ILitExpr i) = show i
    show (FLitExpr f) = show f
    show (InputExpr _ loc) = printf "(%s)" (show loc)
    show (IrrelevantExpr) = "IRRELEVANT"

bits :: ExprT -> Int
bits Int8T = 8
bits Int32T = 32
bits Int64T = 64
bits t = error $ "Unexpected argument to bits: " ++ show t

simplify :: Expr -> Expr
simplify (AddExpr t e1 (ILitExpr 0)) = simplify e1
simplify (AddExpr t (ILitExpr 0) e2) = simplify e2
simplify (AddExpr t e1 e2) = AddExpr t (simplify e1) (simplify e2)
simplify (SubExpr t e1 e2) = SubExpr t (simplify e1) (simplify e2)
simplify (MulExpr t e1 e2) = MulExpr t (simplify e1) (simplify e2)
simplify (DivExpr t e1 e2) = DivExpr t (simplify e1) (simplify e2)
simplify (RemExpr t e1 e2) = RemExpr t (simplify e1) (simplify e2)
simplify (ShlExpr t e1 e2) = ShlExpr t (simplify e1) (simplify e2)
simplify (LshrExpr t e1 e2) = LshrExpr t (simplify e1) (simplify e2)
simplify (AshrExpr _ (ILitExpr 0) _) = ILitExpr 0
simplify (AshrExpr t e1 e2) = AshrExpr t (simplify e1) (simplify e2)
simplify (AndExpr t e1 e2) = AndExpr t (simplify e1) (simplify e2)
simplify (OrExpr t e1 e2) = OrExpr t (simplify e1) (simplify e2)
simplify (XorExpr t e1 e2) = XorExpr t (simplify e1) (simplify e2)
simplify (TruncExpr _ (ZExtExpr _ e)) = simplify e
simplify (TruncExpr _ (SExtExpr _ e)) = simplify e
simplify expr@(TruncExpr t e@(ILitExpr int))
    | int < 2 ^ bits t = e
    | otherwise = expr
simplify (TruncExpr t e) = TruncExpr t (simplify e)
simplify (ZExtExpr t e@ILitExpr{}) = e
simplify (ZExtExpr t e) = ZExtExpr t (simplify e)
simplify (SExtExpr t e@ILitExpr{}) = e -- FIXME: add typing to lits
simplify (SExtExpr t e) = SExtExpr t (simplify e)
simplify (FPTruncExpr t e) = FPTruncExpr t (simplify e)
simplify (FPExtExpr t e) = FPExtExpr t (simplify e)
simplify (FPToSIExpr t e) = FPToSIExpr t (simplify e)
simplify (FPToUIExpr t e) = FPToUIExpr t (simplify e)
simplify (SIToFPExpr t e) = SIToFPExpr t (simplify e)
simplify (UIToFPExpr t e) = UIToFPExpr t (simplify e)
simplify (PtrToIntExpr t1 (IntToPtrExpr t2 e)) = simplify e
simplify (IntToPtrExpr t1 (PtrToIntExpr Int64T e)) = simplify e
simplify (PtrToIntExpr t e) = PtrToIntExpr t (simplify e)
simplify (IntToPtrExpr t e) = IntToPtrExpr t (simplify e)
simplify (BitcastExpr t e) = BitcastExpr t (simplify e)
-- simplify (LoadExpr t e) = LoadExpr t (simplify e)
simplify (BinaryHelperExpr t id e1 e2) = BinaryHelperExpr t id (simplify e1) (simplify e2)
simplify (CastHelperExpr t id e) = CastHelperExpr t id (simplify e)
simplify e = e

-- Simple type system
typeToExprT :: Type -> ExprT
typeToExprT (TypeInteger 8) = Int8T
typeToExprT (TypeInteger 32) = Int32T
typeToExprT (TypeInteger 64) = Int32T
typeToExprT (TypePointer _ _) = PtrT
typeToExprT (TypeFloat) = FloatT
typeToExprT (TypeDouble) = DoubleT
typeToExprT _ = VoidT

exprTOfInst :: Instruction -> ExprT
exprTOfInst = typeToExprT . instructionType

-- Representation of our [partial] knowledge of machine state.
type Info = M.Map Loc Expr

noInfo :: Info
noInfo = M.empty

valueAt :: Loc -> Info -> Expr
valueAt loc =  M.findWithDefault (InputExpr Int64T loc) loc

data BuildExpr a
    = Irrelevant
    | ErrorI String
    | JustI a

instance Monad BuildExpr where
    JustI x >>= f = f x
    Irrelevant >>= _ = Irrelevant
    ErrorI s >>= _ = ErrorI s
    return = JustI
    fail s = ErrorI s

instance Functor BuildExpr where
    fmap f x = x >>= return . f

instance Applicative BuildExpr where
    pure = return
    (<*>) = ap

instance Alternative BuildExpr where
    empty = ErrorI ""
    JustI x <|> _  = JustI x
    Irrelevant <|> _ = Irrelevant
    ErrorI _ <|> JustI x = JustI x
    ErrorI _ <|> Irrelevant = Irrelevant
    ErrorI s <|> ErrorI _ = ErrorI s

buildExprToMaybeExpr :: BuildExpr Expr -> Maybe Expr
buildExprToMaybeExpr (JustI e) = Just e
buildExprToMaybeExpr (ErrorI s) = trace s Nothing
buildExprToMaybeExpr Irrelevant = Just IrrelevantExpr

maybeToM :: (Monad m) => Maybe a -> m a
maybeToM (Just x) = return x
maybeToM (Nothing) = fail ""

instructionToExpr :: Info -> Instruction -> BuildExpr Expr
instructionToExpr info inst = do
    name <- case instructionName inst of
        Just n -> return n
        Nothing -> ErrorI "No name for inst"
    case valueAt (IdLoc name) info of
        IrrelevantExpr -> Irrelevant
        e -> return e

valueContentToExpr :: Info -> ValueContent -> BuildExpr Expr
valueContentToExpr info (ConstantC (ConstantFP _ _ value)) = return $ FLitExpr value 
valueContentToExpr info (ConstantC (ConstantInt _ _ value)) = return $ ILitExpr value
valueContentToExpr info (ConstantC (ConstantValue{ constantInstruction = inst })) = instructionToExpr info inst
valueContentToExpr info (InstructionC inst) = instructionToExpr info inst
valueContentToExpr info (ArgumentC (Argument{ argumentName = name,
                                              argumentType = argType }))
    = return $ InputExpr (typeToExprT argType) (IdLoc name)
valueContentToExpr info val = trace ("Couldn't find expr for " ++ show val) fail ""

valueToExpr :: Info -> Value -> BuildExpr Expr
valueToExpr info = valueContentToExpr info . valueContent

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

binaryInstToExpr :: Info -> Instruction -> BuildExpr Expr
binaryInstToExpr info inst = do
    exprConstructor <- binaryInstToExprConstructor inst
    lhs <- valueToExpr info $ binaryLhs inst
    rhs <- valueToExpr info $ binaryRhs inst
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

castInstToExpr :: Info -> Instruction -> BuildExpr Expr
castInstToExpr info inst = do
    exprConstructor <- castInstToExprConstructor inst
    value <- valueToExpr info $ castedValue inst
    return $ exprConstructor (exprTOfInst inst) value

-- TODO: clean up
loadInstToExpr :: Info -> (Instruction, Maybe MemlogOp) -> BuildExpr Expr
loadInstToExpr info (inst@LoadInst{ loadAddress = addr },
                     Just (AddrMemlogOp LoadOp addrEntry))
    = case addrFlag addrEntry of
        IrrelevantFlag -> Irrelevant -- Ignore parts of CPU state that Panda doesn't track.
        _ -> maybeToM (M.lookup (MemLoc addrEntry) info) <|>
             liftM (LoadExpr $ exprTOfInst inst) (return addrEntry)
      -- liftM (LoadExpr $ exprTOfInst inst) (valueToExpr info addr)
loadInstToExpr _ _ = fail ""

gepInstToExpr :: Info -> Instruction -> BuildExpr Expr
gepInstToExpr info inst@GetElementPtrInst{ _instructionType = instType,
                                           getElementPtrValue = value,
                                           getElementPtrIndices = indices } = do
    valueExpr <- valueToExpr info value
    size <- case instType of
        TypePointer (TypeInteger bits) _ -> return $ bits `quot` 8
        other -> trace ("Type failure: " ++ show other) fail ""
    index <- case map valueContent indices of
        [ConstantC (ConstantInt{ constantIntValue = idx })] -> return idx
        other -> trace ("Value failure: " ++ show other) fail ""
    return $ IntToPtrExpr PtrT $ AddExpr (exprTOfInst inst) valueExpr (ILitExpr $ fromIntegral size * index)
gepInstToExpr _ _ = fail ""

helperInstToExpr :: Info -> Instruction -> BuildExpr Expr
helperInstToExpr info inst@CallInst{ callFunction = funcValue,
                                     callArguments = funcArgs } = case valueContent funcValue of
    ExternalFunctionC (ExternalFunction{ externalFunctionName = funcId })
        | "helper_" `L.isPrefixOf` identifierAsString funcId -> case funcArgs of
            [(argVal, _)] -> do
                argExpr <- valueToExpr info argVal
                return $ CastHelperExpr (exprTOfInst inst) funcId argExpr
            [(argVal1, _), (argVal2, _)] -> do
                 argExpr1 <- valueToExpr info argVal1
                 argExpr2 <- valueToExpr info argVal2
                 return $ BinaryHelperExpr (exprTOfInst inst) funcId argExpr1 argExpr2
            _ -> trace ("Bad funcArgs: " ++ (show funcArgs)) $ fail ""
        | otherwise -> fail ""
    _ -> fail ""
helperInstToExpr _ _ = fail ""

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

(<|||>) :: Alternative f => (a -> b -> f c) -> (a -> b -> f c) -> a -> b -> f c
(<|||>) f1 f2 a b = f1 a b <|> f2 a b

-- List of ways to process instructions and order in which to try them.
instToExprs :: [Info -> Instruction -> BuildExpr Expr]
instToExprs = [ binaryInstToExpr,
                castInstToExpr,
                gepInstToExpr,
                helperInstToExpr ]

memInstToExprs :: [Info -> (Instruction, Maybe MemlogOp) -> BuildExpr Expr]
memInstToExprs = [ loadInstToExpr ]

storeUpdate :: Info -> (Instruction, Maybe MemlogOp) -> Maybe Info
storeUpdate info (inst@StoreInst{ storeIsVolatile = False,
                                  storeValue = val },
                  Just (AddrMemlogOp StoreOp addr)) = do
    -- trace ("STORE: " ++ show inst ++ " ===> " ++ show addr) $ return ()
    value <- buildExprToMaybeExpr $ valueToExpr info val
    return $ M.insert (MemLoc addr) value info
storeUpdate _ _ = fail ""

exprUpdate :: Info -> (Instruction, Maybe MemlogOp) -> Maybe Info
exprUpdate info instOp@(inst, _) = do
    id <- instructionName inst
    let builtExpr = (foldl1 (<|||>) instToExprs) info inst <|>
                     loadInstToExpr info instOp
    expr <- buildExprToMaybeExpr builtExpr
    -- traceShow (id, expr) $ return ()
    return $ M.insert (IdLoc id) (repeatf 5 simplify expr) info
    where repeatf 0 f x = trace "repeatf overflow, bailing" x
          repeatf n f x
              | x == f x = x
              | otherwise = repeatf (n - 1) f $ f x 

-- Ignore alloca and ret instructions
nullUpdate :: Info -> (Instruction, Maybe MemlogOp) -> Maybe Info
nullUpdate info (AllocaInst{}, _) = return info
nullUpdate info (RetInst{}, _) = return info
nullUpdate _ _ = fail ""

infoUpdaters :: [Info -> (Instruction, Maybe MemlogOp) -> Maybe Info]
infoUpdaters = [ exprUpdate, storeUpdate, nullUpdate ]

updateInfo :: Info -> (Instruction, Maybe MemlogOp) -> Info
updateInfo info instOp@(inst, _)
    = fromMaybe (maybeTraceInst inst info) (foldl1 (<|||>) infoUpdaters info instOp)

runBlock :: Info -> MemlogMap -> BasicBlock -> Info
runBlock info memlogMap block = foldl updateInfo info instOpList
    where instOpList = M.findWithDefault (error "Couldn't find basic block instruction list") block memlogMap

deriving instance Show Constant
deriving instance Show ExternalValue
deriving instance Show GlobalAlias
deriving instance Show GlobalVariable
deriving instance Show BasicBlock
deriving instance Show ValueContent

showInfo :: Info -> String
showInfo = unlines . map showEach . filter doShow . M.toList
    where showEach (key, val) = show key ++ " -> " ++ show val
          doShow (_, ILitExpr 0) = False
          doShow (_, IrrelevantExpr) = False
          doShow _ = True

-- data MemlogOp = LoadOp Integer | StoreOp Integer | CondBranchOp Integer
--     deriving (Eq, Ord, Show)

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

getMemlogEntry :: Get MemlogOp
getMemlogEntry = do
    entryType <- getWord64host
    out <- case entryType of
        0 -> AddrMemlogOp <$> getAddrOp <*> getAddrEntry
        1 -> BranchOp <$> getWord32host <* skip 28
        2 -> SelectOp <$> getBool <* skip 28
    -- traceShow out $ return out
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

type MemlogMap = M.Map BasicBlock [(Instruction, Maybe MemlogOp)]
type OpContext = State [MemlogOp]
type MemlogContext = StateT (MemlogMap, String) OpContext
-- Track next basic block to execute
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

associateMemlogWithFunc :: Function -> MemlogContext ()
associateMemlogWithFunc func = addBlock $ head $ functionBody func
    where addBlock :: BasicBlock -> MemlogContext ()
          addBlock block = do
              ops <- lift get
              (associated, nextBlock) <- lift $ runStateT (associateBasicBlock block) Nothing
              (map, funcName) <- get
              if funcName == (identifierAsString $ functionName func)
                  then put (M.insert block associated map, funcName)
                  else return ()
              case nextBlock of
                  Just nextBlock' -> addBlock nextBlock'
                  Nothing -> return ()

associateBasicBlock :: BasicBlock -> FuncOpContext [(Instruction, Maybe MemlogOp)]
associateBasicBlock = mapM associateInstWithCopy . basicBlockInstructions
    where associateInstWithCopy inst = do
              maybeOp <- associateInst inst
              -- case maybeOp of
              --   Just _ -> trace (show (identifierAsString $ functionName $ basicBlockFunction $ fromJust $ instructionBasicBlock inst) ++ ": " ++ show inst ++ "=> " ++  show maybeOp) $ return ()
              --   _ -> return ()
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
        BranchOp branchTaken ->
            if branchTaken == 0
                then put $ Just $ branchTrueTarget inst
                else put $ Just $ branchFalseTarget inst
        _ -> return ()
    return $ Just op
associateInst inst@UnconditionalBranchInst{ unconditionalBranchTarget = target} = do
    put $ Just target
    liftM Just $ memlogPopWithErrorInst inst

associateInst RetInst{} = put Nothing >> return Nothing
associateInst _ = return Nothing

associateFuncs :: [MemlogOp] -> String -> [Function] -> MemlogMap
associateFuncs ops funcName funcs = map
    where ((map, _), leftoverOps) = runState inner ops
          inner = execStateT (mapM_ associateMemlogWithFunc funcs) (M.empty, funcName)

showAssociated :: MemlogMap -> String
showAssociated theMap = L.intercalate "\n\n" $ map showBlock $ M.toList theMap
    where showBlock (block, list) = show (basicBlockName block) ++ ":\n" ++ (L.intercalate "\n" $ map showInstOp list)
          showInstOp (inst, maybeOp) = show inst ++ " => " ++ show maybeOp

main :: IO ()
main = do
    let mainName = "tcg-llvm-tb-1243-400460-main"
    (Right theMod) <- parseLLVMFile defaultParserOptions "/tmp/llvm-mod.bc"
    funcNameList <- lines <$> readFile "/tmp/llvm-functions.log"
    let findFunc name = fromMaybe (error $ "Couldn't find function " ++ name) $ findFunctionByName theMod name
    let funcList = map findFunc funcNameList
    memlogBytes <- B.readFile "/tmp/llvm-memlog.log"
    let memlog = runGet (many getMemlogEntry) memlogBytes
    let associated = associateFuncs memlog mainName funcList
    -- putStrLn $ showAssociated associated
    let basicBlock = seq (associateFuncs memlog mainName funcList) $ head $ functionBody $ findFunc mainName
    putStrLn $ showInfo $ runBlock noInfo associated basicBlock
