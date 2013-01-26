module Expr(Loc(..), ExprT(..), Expr(..), simplify, exprTOfInst, typeToExprT) where

import Data.LLVM.Types
import Text.Printf(printf)

import Memlog(AddrEntry)
import Pretty(Pretty, pretty)

data Loc = IdLoc Function Identifier | MemLoc AddrEntry
    deriving (Eq, Ord)

instance Show Loc where
    show (IdLoc f id) = printf "IdLoc %s %s" (show $ functionName f) (show id)
    show (MemLoc addr) = printf "MemLoc (%s)" (show addr)

instance Pretty Loc where
    pretty (IdLoc f id) = printf "%s: %s" (show $ functionName f) (show id)
    pretty (MemLoc addr) = pretty addr

data ExprT = VoidT | PtrT | Int8T | Int32T | Int64T | FloatT | DoubleT
    deriving (Eq, Ord, Show)

instance Pretty ExprT where
    pretty VoidT = "void"
    pretty PtrT = "ptr"
    pretty Int8T = "i8"
    pretty Int32T = "i32"
    pretty Int64T = "i64"
    pretty FloatT = "flt"
    pretty DoubleT = "dbl"

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
    -- Type, dynamic address, and name.
    LoadExpr ExprT AddrEntry (Maybe String) |
    BinaryHelperExpr ExprT Identifier Expr Expr |
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
    show (TruncExpr _ e) = printf "%s" (show e)
    show (ZExtExpr _ e) = printf "%s" (show e)
    show (SExtExpr _ e) = printf "%s" (show e)
    show (FPTruncExpr _ e) = printf "FPTrunc(%s)" (show e)
    show (FPExtExpr _ e) = printf "FPExt(%s)" (show e)
    show (FPToSIExpr _ e) = printf "FPToSI(%s)" (show e)
    show (FPToUIExpr _ e) = printf "FPToUI(%s)" (show e)
    show (SIToFPExpr _ e) = printf "SIToFP(%s)" (show e)
    show (UIToFPExpr _ e) = printf "UIToFP(%s)" (show e)
    show (PtrToIntExpr _ e) = printf "PtrToInt(%s)" (show e)
    show (IntToPtrExpr _ e) = printf "IntToPtr(%s)" (show e)
    show (BitcastExpr _ e) = printf "Bitcast(%s)" (show e)
    show (LoadExpr _ _ (Just name)) = printf "%%%s" name
    show (LoadExpr _ addr _) = printf "*%s" (pretty addr)
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

