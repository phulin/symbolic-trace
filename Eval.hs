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

type UInt = Word64

data Loc = IdLoc Identifier | MemLoc AddrEntry
    deriving (Eq, Ord, Show)
data Expr =
    AddExpr Expr Expr |
    SubExpr Expr Expr |
    MulExpr Expr Expr |
    DivExpr Expr Expr |
    RemExpr Expr Expr |
    ShlExpr Expr Expr |
    LshrExpr Expr Expr |
    AshrExpr Expr Expr |
    AndExpr Expr Expr |
    OrExpr Expr Expr |
    XorExpr Expr Expr |
    TruncExpr Expr |
    ZExtExpr Expr |
    SExtExpr Expr |
    FPTruncExpr Expr |
    FPExtExpr Expr |
    FPToSIExpr Expr |
    FPToUIExpr Expr |
    SIToFPExpr Expr |
    UIToFPExpr Expr |
    PtrToIntExpr Expr |
    IntToPtrExpr Expr |
    BitcastExpr Expr |
    LoadExpr Expr |
    BinaryHelperExpr Identifier Expr Expr |
    CastHelperExpr Identifier Expr |
    ILitExpr Integer |
    FLitExpr Double |
    InputExpr Loc
    deriving (Eq, Ord, Show)

-- Representation of our [partial] knowledge of machine state.
type Info = M.Map Loc Expr

noInfo :: Info
noInfo = M.empty

valueAt :: Loc -> Info -> Expr
valueAt loc =  M.findWithDefault (InputExpr loc) loc

instructionToExpr :: Info -> Instruction -> Maybe Expr
instructionToExpr info inst = do
    name <- instructionName inst
    return $ valueAt (IdLoc name) info

valueContentToExpr :: Info -> ValueContent -> Maybe Expr
valueContentToExpr info (ConstantC (ConstantFP _ _ value)) = Just $ FLitExpr value 
valueContentToExpr info (ConstantC (ConstantInt _ _ value)) = Just $ ILitExpr value 
valueContentToExpr info (ConstantC (ConstantValue{ constantInstruction = inst })) = instructionToExpr info inst
valueContentToExpr info (InstructionC inst) = instructionToExpr info inst
valueContentToExpr info (ArgumentC (Argument{ argumentName = name })) = Just $ InputExpr (IdLoc name)
valueContentToExpr info val = trace ("Couldn't find expr for " ++ show val) Nothing

valueToExpr :: Info -> Value -> Maybe Expr
valueToExpr info = valueContentToExpr info . valueContent

binaryInstToExprConstructor :: Instruction -> Maybe (Expr -> Expr -> Expr)
binaryInstToExprConstructor AddInst{} = Just AddExpr
binaryInstToExprConstructor SubInst{} = Just SubExpr
binaryInstToExprConstructor MulInst{} = Just MulExpr
binaryInstToExprConstructor DivInst{} = Just DivExpr
binaryInstToExprConstructor RemInst{} = Just RemExpr
binaryInstToExprConstructor ShlInst{} = Just ShlExpr
binaryInstToExprConstructor LshrInst{} = Just LshrExpr
binaryInstToExprConstructor AshrInst{} = Just AshrExpr
binaryInstToExprConstructor AndInst{} = Just AndExpr
binaryInstToExprConstructor OrInst{} = Just OrExpr
binaryInstToExprConstructor XorInst{} = Just XorExpr
binaryInstToExprConstructor _ = Nothing

binaryInstToExpr :: Info -> Instruction -> Maybe Expr
binaryInstToExpr info inst = do
    exprConstructor <- binaryInstToExprConstructor inst
    lhs <- valueToExpr info $ binaryLhs inst
    rhs <- valueToExpr info $ binaryRhs inst
    return $ exprConstructor lhs rhs

castInstToExprConstructor :: Instruction -> Maybe (Expr -> Expr)
castInstToExprConstructor TruncInst{} = Just TruncExpr
castInstToExprConstructor ZExtInst{} = Just ZExtExpr
castInstToExprConstructor SExtInst{} = Just SExtExpr
castInstToExprConstructor FPTruncInst{} = Just FPTruncExpr
castInstToExprConstructor FPExtInst{} = Just FPExtExpr
castInstToExprConstructor FPToSIInst{} = Just FPToSIExpr
castInstToExprConstructor FPToUIInst{} = Just FPToUIExpr
castInstToExprConstructor SIToFPInst{} = Just SIToFPExpr
castInstToExprConstructor UIToFPInst{} = Just UIToFPExpr
castInstToExprConstructor PtrToIntInst{} = Just PtrToIntExpr
castInstToExprConstructor IntToPtrInst{} = Just IntToPtrExpr
castInstToExprConstructor BitcastInst{} = Just BitcastExpr
castInstToExprConstructor _ = Nothing

castInstToExpr :: Info -> Instruction -> Maybe Expr
castInstToExpr info inst = do
    exprConstructor <- castInstToExprConstructor inst
    value <- valueToExpr info $ castedValue inst
    return $ exprConstructor value

-- TODO: clean up
loadInstToExpr :: Info -> (Instruction, Maybe MemlogOp) -> Maybe Expr
loadInstToExpr info (inst@LoadInst{ loadAddress = addr },
                     Just (AddrMemlogOp LoadOp addrEntry)) = do
    -- trace ("LOAD: " ++ show inst ++ " ===> " ++ show addrEntry) $ return ()
    M.lookup (MemLoc addrEntry) info <|> liftM LoadExpr (valueToExpr info addr)
loadInstToExpr _ _ = Nothing

gepInstToExpr :: Info -> Instruction -> Maybe Expr
gepInstToExpr info inst@GetElementPtrInst{ _instructionType = instType,
                                           getElementPtrValue = value,
                                           getElementPtrIndices = indices } = do
    valueExpr <- valueToExpr info value
    size <- case instType of
        TypePointer (TypeInteger bits) _ -> Just $ bits `quot` 8
        other -> trace ("Type failure: " ++ show other) Nothing
    index <- case map valueContent indices of
        [ConstantC (ConstantInt{ constantIntValue = idx })] -> Just idx
        other -> trace ("Value failure: " ++ show other) Nothing
    return $ IntToPtrExpr $ AddExpr valueExpr (ILitExpr $ fromIntegral size * index)
gepInstToExpr _ _ = Nothing

helperInstToExpr :: Info -> Instruction -> Maybe Expr
helperInstToExpr info inst@CallInst{ callFunction = funcValue,
                                     callArguments = funcArgs } = case valueContent funcValue of
    ExternalFunctionC (ExternalFunction{ externalFunctionName = funcId })
        | "helper_" `L.isPrefixOf` identifierAsString funcId -> case funcArgs of
            [(argVal, _)] -> do
                argExpr <- valueToExpr info argVal
                return $ CastHelperExpr funcId argExpr
            [(argVal1, _), (argVal2, _)] -> do
                argExpr1 <- valueToExpr info argVal1
                argExpr2 <- valueToExpr info argVal2
                return $ BinaryHelperExpr funcId argExpr1 argExpr2
            _ -> trace ("Bad funcArgs: " ++ (show funcArgs)) Nothing
        | otherwise -> Nothing
    _ -> Nothing
helperInstToExpr _ _ = Nothing

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
instToExprs :: [Info -> Instruction -> Maybe Expr]
instToExprs = [ binaryInstToExpr,
                castInstToExpr,
                gepInstToExpr,
                helperInstToExpr ]

memInstToExprs :: [Info -> (Instruction, Maybe MemlogOp) -> Maybe Expr]
memInstToExprs = [ loadInstToExpr ]

storeUpdate :: Info -> (Instruction, Maybe MemlogOp) -> Maybe Info
storeUpdate info (inst@StoreInst{ storeIsVolatile = False,
                                  storeValue = val },
                  Just (AddrMemlogOp StoreOp addr)) = do
    trace ("STORE: " ++ show inst ++ " ===> " ++ show addr) $ return ()
    value <- valueToExpr info val
    return $ M.insert (MemLoc addr) value info
storeUpdate _ _ = Nothing

exprUpdate :: Info -> (Instruction, Maybe MemlogOp) -> Maybe Info
exprUpdate info instOp@(inst, _) = do
    id <- instructionName inst
    expr <- (foldl1 (<|||>) instToExprs) info inst <|>
            loadInstToExpr info instOp
    -- traceShow (id, expr) $ return ()
    return $ M.insert (IdLoc id) expr info

-- Ignore alloca and ret instructions
nullUpdate :: Info -> (Instruction, Maybe MemlogOp) -> Maybe Info
nullUpdate info (AllocaInst{}, _) = Just info
nullUpdate info (RetInst{}, _) = Just info
nullUpdate _ _ = Nothing

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
showInfo = unlines . map showEach . M.toList
    where showEach (key, val) = show key ++ " -> " ++ show val

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
