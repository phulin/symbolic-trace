-- Symbolic evaluator for basic bidks

module Main where

import Data.LLVM.Types
import LLVM.Parse
import qualified Data.Map as M
import qualified Data.Bits as B
import Data.Word
import Control.Applicative
import Data.Maybe

-- Instruction representation
type Addr = Word64
type UInt = Word64

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
    InputExpr Identifier
    deriving (Eq, Ord, Show)
-- Representation of our [partial] knowledge of machine state.
type Info = M.Map Identifier Expr

noInfo :: Info
noInfo = M.empty

-- simplify :: Expr -> Expr
-- simplify (AddExpr (LitExpr l1) (LitExpr l2)) = LitExpr $ l1 + l2
-- simplify (AddExpr (LitExpr 0) e) = e
-- simplify (AddExpr e (LitExpr 0)) = e
-- simplify (MulExpr (LitExpr l1) (LitExpr l2)) = LitExpr $ l1 * l2 
-- simplify (MulExpr (LitExpr 0) e) = LitExpr 0
-- simplify (MulExpr e (LitExpr 0)) = LitExpr 0
-- simplify (MulExpr (LitExpr 1) e) = e
-- simplify (MulExpr e (LitExpr 1)) = e
-- simplify (XorExpr (LitExpr l1) (LitExpr l2)) = LitExpr $ B.xor l1 l2
-- simplify (XorExpr (LitExpr 0) e) = e
-- simplify (XorExpr e (LitExpr 0)) = e
-- simplify e@(XorExpr e1 e2)
--     | e1 == e2 = LitExpr 0
--     | otherwise = e
-- simplify e = e

valueAt :: Identifier -> Info -> Expr
valueAt id =  M.findWithDefault (InputExpr id) id

valueContentToLitExpr :: ValueContent -> Maybe Expr
valueContentToLitExpr (ConstantC (ConstantFP _ _ value)) = Just $ FLitExpr value 
valueContentToLitExpr (ConstantC (ConstantInt _ _ value)) = Just $ ILitExpr value 
valueContentToLitExpr _ = Nothing

valueToLitExpr :: Value -> Maybe Expr
valueToLitExpr = valueContentToLitExpr . valueContent

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

binaryInstToExpr :: Instruction -> Maybe Expr
binaryInstToExpr inst = do
    exprConstructor <- binaryInstToExprConstructor inst
    lhs <- valueToLitExpr $ binaryLhs inst
    rhs <- valueToLitExpr $ binaryRhs inst
    return $ exprConstructor lhs rhs

unaryInstToExprConstructor :: Instruction -> Maybe (Expr -> Expr)
unaryInstToExprConstructor TruncInst{} = Just TruncExpr
unaryInstToExprConstructor ZExtInst{} = Just ZExtExpr
unaryInstToExprConstructor SExtInst{} = Just SExtExpr
unaryInstToExprConstructor FPTruncInst{} = Just FPTruncExpr
unaryInstToExprConstructor FPExtInst{} = Just FPExtExpr
unaryInstToExprConstructor FPToSIInst{} = Just FPToSIExpr
unaryInstToExprConstructor FPToUIInst{} = Just FPToUIExpr
unaryInstToExprConstructor SIToFPInst{} = Just SIToFPExpr
unaryInstToExprConstructor UIToFPInst{} = Just UIToFPExpr
unaryInstToExprConstructor _ = Nothing

unaryInstToExpr :: Instruction -> Maybe Expr
unaryInstToExpr inst = do
    exprConstructor <- unaryInstToExprConstructor inst
    value <- valueToLitExpr $ castedValue inst
    return $ exprConstructor value

updateInfo :: Info -> Instruction -> Info
updateInfo info inst = fromMaybe info $ do
    id <- instructionName inst
    expr <- (binaryInstToExpr inst) <|> (unaryInstToExpr inst)
    return $ M.insert id expr info

runBlock :: Info -> BasicBlock -> Info
runBlock info block = foldl updateInfo info $ basicBlockInstructions block

main :: IO ()
main = do
    (Right theMod) <- parseLLVMFile defaultParserOptions "/home/phulin/UROP/invsqrt.bc"
    print $ map functionName $ moduleDefinedFunctions theMod

