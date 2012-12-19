-- Symbolic evaluator for basic blocks

module Main where

import Data.LLVM.Types
import LLVM.Parse
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Bits as B
import Data.Word
import Control.Applicative
import Data.Maybe
import Debug.Trace

type Addr = Word64
type UInt = Word64

data Loc = IdLoc Identifier | MemLoc Addr
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

loadInstToExpr :: Info -> Instruction -> Maybe Expr
loadInstToExpr info inst@LoadInst{ loadAddress = addr } = do
    addrExpr <- valueToExpr info addr
    return $ LoadExpr addrExpr
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
        | (identifierAsString $ externalFunctionName func) == "printdynval" -> id
        | otherwise -> traceInst inst
    _ -> traceInst inst
maybeTraceInst inst = traceInst inst

(<||>) :: Alternative f => (a -> f b) -> (a -> f b) -> a -> f b
(<||>) f1 f2 a = f1 a <|> f2 a

(<|||>) :: Alternative f => (a -> b -> f c) -> (a -> b -> f c) -> a -> b -> f c
(<|||>) f1 f2 a b = f1 a b <|> f2 a b

-- List of ways to process instructions and order in which to try them.
instToExprs :: [Info -> Instruction -> Maybe Expr]
instToExprs = [ binaryInstToExpr,
                castInstToExpr,
                loadInstToExpr,
                gepInstToExpr,
                helperInstToExpr ]

updateInfo :: Info -> Instruction -> Info
updateInfo info inst = fromMaybe (maybeTraceInst inst info) $ do
    id <- instructionName inst
    expr <- (foldl1 (<|||>) instToExprs) info inst
    return $ M.insert (IdLoc id) expr info

runBlock :: Info -> BasicBlock -> Info
runBlock info block = foldl updateInfo info $ basicBlockInstructions block

deriving instance Show Constant
deriving instance Show ExternalValue
deriving instance Show GlobalAlias
deriving instance Show GlobalVariable
deriving instance Show BasicBlock
deriving instance Show ValueContent

showInfo :: Info -> String
showInfo = unlines . map showEach . M.toList
    where showEach (key, val) = show key ++ " -> " ++ show val

main :: IO ()
main = do
    (Right theMod) <- parseLLVMFile defaultParserOptions "/tmp/llvm-mod.bc"
    let func = fromMaybe (error "Couldn't find function") $ findFunctionByName theMod "tcg-llvm-tb-1229-4004a0-main"
    let basicBlock = head $ functionBody $ func
    putStrLn $ showInfo $ runBlock noInfo basicBlock
