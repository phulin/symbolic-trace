-- Symbolic evaluator for basic blocks

module Main where

import Data.LLVM.Types
import LLVM.Parse
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

valueContentToExpr :: Info -> ValueContent -> Maybe Expr
valueContentToExpr info (ConstantC (ConstantFP _ _ value)) = Just $ FLitExpr value 
valueContentToExpr info (ConstantC (ConstantInt _ _ value)) = Just $ ILitExpr value 
valueContentToExpr info (InstructionC inst) = do
    name <- instructionName inst
    return $ valueAt name info
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
castInstToExprConstructor _ = Nothing

castInstToExpr :: Info -> Instruction -> Maybe Expr
castInstToExpr info inst = do
    exprConstructor <- castInstToExprConstructor inst
    value <- valueToExpr info $ castedValue inst
    return $ exprConstructor value

updateInfo :: Info -> Instruction -> Info
updateInfo info inst = fromMaybe info $ do
    id <- instructionName inst
    expr <- (binaryInstToExpr info inst) <|> (castInstToExpr info inst)
    return $ M.insert id expr info

runBlock :: Info -> BasicBlock -> Info
runBlock info block = foldl updateInfo info $ basicBlockInstructions block

deriving instance Show Constant
deriving instance Show ExternalValue
deriving instance Show GlobalAlias
deriving instance Show GlobalVariable
deriving instance Show BasicBlock
deriving instance Show ValueContent

main :: IO ()
main = do
    (Right theMod) <- parseLLVMFile defaultParserOptions "/home/phulin/UROP/invsqrt.bc"
    let basicBlock = head $ functionBody $ head $ moduleDefinedFunctions theMod
    print $ runBlock noInfo basicBlock
