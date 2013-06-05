module Expr(Loc(..), ExprT(..), Expr(..), simplify, exprTOfInst, typeToExprT, ExprFolders(..), constFolders, foldExpr) where

import Debug.Trace

import Data.Bits((.&.), (.|.), xor)
import Data.LLVM.Types
import Text.Printf(printf)

import Memlog(AddrEntry(..), AddrEntryType(..))
import Pretty(Pretty, pretty)

import qualified Data.List as L

data Loc = IdLoc Function Identifier | MemLoc AddrEntry
    deriving (Eq, Ord)

instance Show Loc where
    show (IdLoc f id) = printf "IdLoc %s %s" (show $ functionName f) (show id)
    show (MemLoc addr) = printf "MemLoc (%s)" (show addr)

instance Pretty Loc where
    pretty (IdLoc f id) = printf "%s: %s" (show $ functionName f) (show id)
    pretty (MemLoc addr) = pretty addr

data ExprT = VoidT | PtrT | Int8T | Int32T | Int64T | FloatT | DoubleT
    | StructT [ExprT]
    deriving (Eq, Ord, Show)

instance Pretty ExprT where
    pretty VoidT = "void"
    pretty PtrT = "ptr"
    pretty Int8T = "i8"
    pretty Int32T = "i32"
    pretty Int64T = "i64"
    pretty FloatT = "flt"
    pretty DoubleT = "dbl"

instance Pretty CmpPredicate where
    pretty ICmpEq = "=="
    pretty ICmpNe = "!="
    pretty ICmpSgt = ">s"
    pretty ICmpSge = ">=s"
    pretty ICmpSlt = "<s"
    pretty ICmpSle = "<=s"
    pretty ICmpUgt = ">u"
    pretty ICmpUge = ">=u"
    pretty ICmpUlt = "<u"
    pretty ICmpUle = "<=u"
    pretty p = "?" ++ (show p) ++ "?"

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
    ICmpExpr CmpPredicate Expr Expr |
    ILitExpr Integer | -- takes any integer type
    FLitExpr Double | -- takes any float type
    InputExpr ExprT Loc |
    IntrinsicExpr ExprT ExternalFunction [Expr] |
    ExtractExpr ExprT Int Expr |
    GEPExpr | -- dummy expression for getelementptr instructions
    IrrelevantExpr
    deriving (Eq, Ord)

instance Show Expr where
    show (AddExpr _ e1 e2) = printf "(%s + %s)" (show e1) (show e2)
    show (SubExpr _ e1 e2) = printf "(%s - %s)" (show e1) (show e2)
    show (MulExpr _ e1 e2) = printf "(%s * %s)" (show e1) (show e2)
    show (DivExpr _ e1 e2) = printf "(%s / %s)" (show e1) (show e2)
    show (RemExpr _ e1 e2) = printf "(%s %% %s)" (show e1) (show e2)
    show (ShlExpr _ e1 e2) = printf "(%s << %s)" (show e1) (show e2)
    show (LshrExpr _ e1 e2) = printf "(%s L>> %s)" (show e1) (show e2)
    show (AshrExpr _ e1 e2) = printf "(%s A>> %s)" (show e1) (show e2)
    show (AndExpr _ e1 e2) = printf "(%s & %s)" (show e1) (show e2)
    show (OrExpr _ e1 e2) = printf "(%s | %s)" (show e1) (show e2)
    show (XorExpr _ e1 e2) = printf "(%s ^ %s)" (show e1) (show e2)
    show (TruncExpr t e) = printf "T%d(%s)" (bits t) (show e)
    show (ZExtExpr t e) = printf "ZX%d(%s)" (bits t) (show e)
    show (SExtExpr t e) = printf "SX%d(%s)" (bits t) (show e)
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
    show (LoadExpr _ addr@AddrEntry{ addrType = GReg } _) = printf "%s" (pretty addr)
    show (LoadExpr _ addr _) = printf "*%s" (pretty addr)
    show (ICmpExpr pred e1 e2) = printf "%s %s %s" (show e1) (pretty pred) (show e2)
    show (ILitExpr i) = if i >= 256 then printf "0x%x" i else show i
    show (FLitExpr f) = show f
    show (InputExpr _ loc) = printf "(%s)" (show loc)
    show (IntrinsicExpr _ f es) = printf "%s(%s)" (show $ externalFunctionName f)
        (L.intercalate ", " $ map show es)
    show (ExtractExpr _ idx e) = printf "%s[%d]" (show e) idx
    show (GEPExpr) = "GEP"
    show (IrrelevantExpr) = "IRRELEVANT"

data ExprFolders a = ExprFolders {
    iLitFolder :: Integer -> a,
    fLitFolder :: Double -> a,
    inputFolder :: ExprT -> Loc -> a,
    loadFolder :: ExprT -> AddrEntry -> Maybe String -> a,
    irrelevantFolder :: a,
    binaryCombiner :: a -> a -> a
}

constFolders :: a -> ExprFolders a
constFolders x = ExprFolders {
    iLitFolder = const x,
    fLitFolder = const x,
    inputFolder = const $ const x,
    loadFolder = const $ const $ const x,
    irrelevantFolder = x,
    binaryCombiner = const $ const x
}

foldExpr :: ExprFolders a -> Expr -> a
foldExpr fs (AddExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (SubExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (MulExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (DivExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (RemExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (ShlExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (LshrExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (AshrExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (AndExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (OrExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (XorExpr t e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (TruncExpr t e) = foldExpr fs e
foldExpr fs (ZExtExpr t e) = foldExpr fs e
foldExpr fs (SExtExpr t e) = foldExpr fs e
foldExpr fs (FPTruncExpr t e) = foldExpr fs e
foldExpr fs (FPExtExpr t e) = foldExpr fs e
foldExpr fs (FPToSIExpr t e) = foldExpr fs e
foldExpr fs (FPToUIExpr t e) = foldExpr fs e
foldExpr fs (SIToFPExpr t e) = foldExpr fs e
foldExpr fs (UIToFPExpr t e) = foldExpr fs e
foldExpr fs (PtrToIntExpr t e) = foldExpr fs e
foldExpr fs (IntToPtrExpr t e) = foldExpr fs e
foldExpr fs (BitcastExpr t e) = foldExpr fs e
foldExpr fs (LoadExpr t addr name) = loadFolder fs t addr name
foldExpr fs (ICmpExpr pred e1 e2) = binaryCombiner fs (foldExpr fs e1) (foldExpr fs e2)
foldExpr fs (ILitExpr i) = iLitFolder fs i
foldExpr fs (FLitExpr f) = fLitFolder fs f
foldExpr fs (InputExpr t loc) = inputFolder fs t loc
foldExpr fs (IntrinsicExpr _ _ args) = foldl1 (binaryCombiner fs) (map (foldExpr fs) args)
foldExpr fs (ExtractExpr _ _ e) = foldExpr fs e
foldExpr fs (GEPExpr) = irrelevantFolder fs
foldExpr fs (IrrelevantExpr) = irrelevantFolder fs

bits :: ExprT -> Int
bits Int8T = 8
bits Int32T = 32
bits Int64T = 64
bits t = error $ "Unexpected argument to bits: " ++ show t

simplify :: Expr -> Expr
simplify (AddExpr t e1 (ILitExpr 0)) = simplify e1
simplify (AddExpr t (ILitExpr 0) e2) = simplify e2
simplify (AddExpr t (ILitExpr a) (ILitExpr b)) = ILitExpr $ a + b
simplify (AddExpr ta (MulExpr tm e1 e2) e3)
    | e1 == e3 = simplify $ MulExpr ta e1 (AddExpr tm e2 (ILitExpr 1))
simplify (AddExpr t (AddExpr _ e1 (ILitExpr a)) (ILitExpr b))
    = simplify $ AddExpr t e1 (ILitExpr $ a + b)
simplify (AddExpr _ (SubExpr _ e1 e2) e3)
    | e2 == e3 = simplify e1
simplify (AddExpr t e1 e2)
    | e1 == e2 = simplify $ MulExpr t e1 (ILitExpr 2)
simplify (AddExpr t e1 e2) = AddExpr t (simplify e1) (simplify e2)
simplify (SubExpr t (ILitExpr a) (ILitExpr b)) = ILitExpr $ a - b
simplify (SubExpr t e1 (ILitExpr b)) = simplify $ AddExpr t e1 (ILitExpr $ -b)
simplify (SubExpr t e1 e2)
    | e1 == e2 = ILitExpr 0
simplify (SubExpr ta (MulExpr tm e1 e2) e3)
    | e1 == e3 = simplify $ MulExpr ta e1 (SubExpr tm e2 (ILitExpr 1))
simplify (SubExpr t (AddExpr _ e1 e2) (AddExpr _ e3 e4))
    | e1 == e3 = simplify $ SubExpr t e2 e4
simplify (SubExpr t e1 e2) = SubExpr t (simplify e1) (simplify e2)
simplify (MulExpr t (ILitExpr a) (ILitExpr b)) = ILitExpr $ a * b
simplify (MulExpr t e (ILitExpr 1)) = simplify e
simplify (MulExpr t e1 e2) = MulExpr t (simplify e1) (simplify e2)
simplify (DivExpr t e1 e2) = DivExpr t (simplify e1) (simplify e2)
simplify (RemExpr t e1 e2) = RemExpr t (simplify e1) (simplify e2)
simplify (ShlExpr t e1 (ILitExpr i))
    | i >= 0 = simplify $ MulExpr t e1 (ILitExpr $ 2 ^ i)
simplify (ShlExpr t e1 e2) = ShlExpr t (simplify e1) (simplify e2)
simplify (LshrExpr t e1 e2) = LshrExpr t (simplify e1) (simplify e2)
simplify (AshrExpr _ (ILitExpr 0) _) = ILitExpr 0
simplify (AshrExpr t e1 e2) = AshrExpr t (simplify e1) (simplify e2)
simplify (AndExpr t (ILitExpr a) (ILitExpr b)) = ILitExpr $ a .&. b
simplify (AndExpr _ (ZExtExpr _ e@(LoadExpr Int8T _ _)) (ILitExpr 255)) = simplify e
simplify (AndExpr Int32T e (ILitExpr 0xFFFFFFFF)) = simplify e
simplify (AndExpr Int64T e (ILitExpr 0xFFFFFFFF))
    = simplify $ ZExtExpr Int64T $ TruncExpr Int32T e
simplify (AndExpr t e1 e2) = AndExpr t (simplify e1) (simplify e2)
simplify (OrExpr t (ILitExpr a) (ILitExpr b)) = ILitExpr $ a .|. b
simplify (OrExpr t e1 e2) = OrExpr t (simplify e1) (simplify e2)
simplify (XorExpr t e1 e2) = XorExpr t (simplify e1) (simplify e2)
-- FIXME: HACK!!!!
--simplify (ZExtExpr _ e) = simplify e
--simplify (SExtExpr _ e) = simplify e
--simplify (TruncExpr _ e) = simplify e
simplify (TruncExpr t1 (ZExtExpr t2 e))
    | t1 == t2 = simplify e
    | bits t1 < bits t2 = simplify $ TruncExpr t1 e
simplify (TruncExpr t1 (SExtExpr t2 e))
    | t1 == t2 = simplify e
    | bits t1 < bits t2 = simplify $ TruncExpr t1 e
simplify expr@(TruncExpr t e@(ILitExpr int))
    | int < 2 ^ bits t = e
    | otherwise = expr
simplify (ZExtExpr t e@ILitExpr{}) = e
simplify (ZExtExpr t1 (TruncExpr t2 e))
    | t1 == t2 = simplify $ TruncExpr t2 e
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
simplify (ICmpExpr p (SubExpr _ e1 e2) (ILitExpr 0))
    = simplify $ ICmpExpr p e1 e2
simplify (ICmpExpr ICmpEq (XorExpr _ e1 e2) (ILitExpr 0))
    = simplify $ ICmpExpr ICmpEq e1 e2
simplify (ICmpExpr p (AndExpr _ e1 e2) (ILitExpr 0))
    | e1 == e2 && (p == ICmpEq || p == ICmpNe)
        = simplify $ ICmpExpr ICmpEq e1 (ILitExpr 0)
simplify (ICmpExpr p e1 e2) = ICmpExpr p (simplify e1) (simplify e2)
simplify (IntrinsicExpr t f es) = IntrinsicExpr t f $ map simplify es
simplify (ExtractExpr t idx e) = ExtractExpr t idx (simplify e)
simplify e = e

-- Simple type system
typeToExprT :: Type -> ExprT
typeToExprT (TypeInteger 8) = Int8T
typeToExprT (TypeInteger 32) = Int32T
typeToExprT (TypeInteger 64) = Int32T
typeToExprT (TypePointer _ _) = PtrT
typeToExprT (TypeFloat) = FloatT
typeToExprT (TypeDouble) = DoubleT
typeToExprT (TypeStruct _ ts _) = StructT $ map typeToExprT ts
typeToExprT _ = VoidT

exprTOfInst :: Instruction -> ExprT
exprTOfInst = typeToExprT . instructionType

