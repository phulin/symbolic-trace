-- Symbolic evaluator for basic bidks

module Main where

import qualified Data.LLVM.Types as LT
import LLVM.Parse
import qualified Data.Map as M
import qualified Data.Bits as B
import Data.Word

-- Instruction representation
type Addr = Word64
type UInt = Word64

data Expr a =
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
    ILitExpr UInt |
    FLitExpr Double |
    InputExpr Loc
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

mathUpdate :: (Expr -> Expr -> Expr) -> Reg -> Reg -> Info -> Info
mathUpdate exprBin srcReg dstReg info = M.insert (RegLoc dstReg) newExpr info
    where newExpr = simplify $ exprBin (valueAt (RegLoc srcReg) info) (valueAt (RegLoc dstReg) info)

valueToLitExpr :: Value -> Expr
valueToLitExpr = undefined

updateInfo :: Info -> Instruction -> Info
updateInfo info (AddInst _ _ _ _ _ _ lhs rhs) = M.insert (id) (AddExpr (valueToLitExpr lhs) (valueToLitExpr rhs))
updateInfo info _ = info
-- updateInfo info (Mov srcLoc dstLoc) = M.insert dstLoc (valueAt srcLoc info) info
-- updateInfo info (Add srcReg dstReg) = (mathUpdate AddExpr srcReg dstReg) info
-- updateInfo info (Mul srcReg dstReg) = (mathUpdate MulExpr srcReg dstReg) info
-- updateInfo info (Xor srcReg dstReg) = (mathUpdate XorExpr srcReg dstReg) info
-- updateInfo info (Put value dstLoc) = M.insert dstLoc (LitExpr value) info

runInstrs :: Info -> BasicBlock -> Info
runInstrs = foldl updateInfo

main :: IO ()
main = do
    (Right theMod) <- parseLLVMFile defaultParserOptions "/tmp/llvm-mod.bc"
    print $ map (LT.identifierAsString . LT.functionName) $ LT.moduleDefinedFunctions theMod

