module Expr(simplify, exprTOfInst, typeToExprT, idLoc, renderExpr) where

import Debug.Trace

import Control.Applicative((<$>))
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.RWS(RWS, evalRWS)
import Data.Bits((.&.), (.|.), xor, shiftL, shiftR)
import Data.LLVM.Types
import Data.Word(Word8, Word16, Word32, Word64)
import Text.PrettyPrint
import Text.Printf(printf)

import Data.RESET.Types
import Memlog(AddrEntry(..), AddrEntryType(..))
import Pretty(Pretty, pretty)

import qualified Data.List as L

idLoc :: Function -> Identifier -> Loc
idLoc f id = IdLoc (functionName f) id

instance Show Loc where
    show (IdLoc f id) = printf "IdLoc %s %s" (show f) (show id)
    show (MemLoc addr) = printf "MemLoc (%s)" (show addr)

instance Pretty Loc where
    pretty (IdLoc f id) = printf "%s: %s" (show f) (show id)
    pretty (MemLoc addr) = pretty addr

instance Pretty ExprT where
    pretty VoidT = "void"
    pretty PtrT = "ptr"
    pretty Int1T = "i1"
    pretty Int8T = "i8"
    pretty Int16T = "i16"
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

renderExpr :: ExprOptions -> Expr -> String
renderExpr opts e = render $ fst $ evalRWS (sh $ repeatf 50 simplify e) opts 0
    where render = renderStyle style{ mode = OneLineMode }

instance Show Expr where
    show = renderExpr defaultExprOptions

-- Inside ShowExpr, can read ExprOptions and set precedence.
type ShowExpr = RWS ExprOptions () Int

-- Convenience operators for monadic Docs
(<<+>>) = liftM2 (<+>)
(<<>>) = liftM2 (<>)
a <+>> mb = return a <<+>> mb
ma <<+> b = ma <<+>> return b
a <>> mb = return a <<>> mb
ma <<> b = ma <<>> return b

-- Render an expression inside a different precedence context
withPrec :: Int -> ShowExpr a -> ShowExpr a
withPrec prec act = do
    contextPrec <- get
    put prec
    result <- act
    put contextPrec
    return result

-- Parenthesize if precedence requires
-- Type is SE Doc -> SE Doc for syntactical convenience
parensPrec :: Int -> ShowExpr Doc -> ShowExpr Doc
parensPrec prec mdoc = do
    doc <- mdoc
    contextPrec <- get
    withPrec prec $ if prec >= contextPrec
        then mdoc
        else parens <$> mdoc

-- Make parentheses and reset precedence
parens0 :: ShowExpr Doc -> ShowExpr Doc
parens0 = parensPrec 0

-- Associate left, right, always, or never (i.e., where to parenthesize operands)
data Infix = AssocL | AssocR | AssocA | AssocN

-- Binary operator: expr1 op expr2
bin :: Infix -> Int -> String -> Expr -> Expr -> ShowExpr Doc
bin inf prec op e1 e2 = parensPrec prec $ shl e1 <<+> text op <<+>> shr e2
    where (shl, shr) = case inf of
              AssocL -> (sh, shHighPrec)
              AssocR -> (shHighPrec, sh)
              AssocA -> (sh, sh)
              AssocN -> (shHighPrec, shHighPrec)

-- Unary operator: func(expr)
un :: String -> Expr -> ShowExpr Doc
un func e = text func <>> (parens0 $ sh e)

-- Same as un, but show only if exprShowCasts is true.
-- Otherwise just show casted expression
cast :: String -> Expr -> ShowExpr Doc
cast func e = do
    showCasts <- asks exprShowCasts
    if showCasts then un func e else sh e

-- e1, e2, e3, ..., e9
-- We don't want to parenthesize interior expressions, so we use shNoPrec
commas :: [Expr] -> ShowExpr Doc
commas es = hsep <$> punctuate (text ",") <$> mapM shNoPrec es

-- (e1, e2, e3, ..., e9)
tuple :: [Expr] -> ShowExpr Doc
tuple es = parens0 $ commas es 

-- Guarantee to not parenthesize the inner expression.
shNoPrec :: Expr -> ShowExpr Doc
shNoPrec = withPrec 0 . sh

-- Guarantee to parenthesize inner expression
shHighPrec :: Expr -> ShowExpr Doc
shHighPrec = withPrec 10000 . sh

sh :: Expr -> ShowExpr Doc
sh (AddExpr _ e1 e2) = bin AssocA 10 "+" e1 e2
sh (SubExpr _ e1 e2) = bin AssocL 10 "-" e1 e2
sh (MulExpr _ e1 e2) = bin AssocA 20 "*" e1 e2
sh (DivExpr _ e1 e2) = bin AssocL 20 "/" e1 e2
sh (RemExpr _ e1 e2) = bin AssocL 15 "%%" e1 e2
sh (ShlExpr _ e1 e2) = bin AssocN 40 "<<" e1 e2
sh (LshrExpr _ e1 e2) = bin AssocN 40 "L>>" e1 e2
sh (AshrExpr _ e1 e2) = bin AssocN 40 "A>>" e1 e2
sh (AndExpr _ e1 e2) = bin AssocN 35 "&" e1 e2
sh (OrExpr _ e1 e2) = bin AssocN 30 "|" e1 e2
sh (XorExpr _ e1 e2) = bin AssocN 25 "^" e1 e2
sh (TruncExpr t e) = cast (printf "T%d" (bits t)) e
sh (ZExtExpr t e) = cast (printf "ZX%d" (bits t)) e
sh (SExtExpr t e) = cast (printf "SX%d" (bits t)) e
sh (FPTruncExpr _ e) = cast "FPTrunc" e
sh (FPExtExpr _ e) = cast "FPExt" e
sh (FPToSIExpr _ e) = cast "FPToSI" e
sh (FPToUIExpr _ e) = cast "FPToUI" e
sh (SIToFPExpr _ e) = cast "SIToFP" e
sh (UIToFPExpr _ e) = cast "UIToFP" e
sh (PtrToIntExpr _ e) = cast "PtrToInt" e
sh (IntToPtrExpr _ e) = cast "IntToPtr" e
sh (BitcastExpr t e) = un (printf "Bitcast%s" (show t)) e
sh (LoadExpr _ _ (Just name)) = return $ text "%" <> text name
sh (LoadExpr _ addr@AddrEntry{ addrType = GReg } _) = return $ text $ pretty addr
sh (LoadExpr _ addr _) = return $ text "*" <> text (pretty addr)
sh (ICmpExpr pred e1 e2) = bin AssocL 0 (pretty pred) e1 e2
-- Print in hex if >=256 (probably an address); otherwise print in decimal
sh (ILitExpr i) = return $ if i >= 256 then text $ printf "0x%x" i else integer i
sh (FLitExpr f) = return $ text $ printf "%.1ff" f 
sh (InputExpr _ loc) = return $ parens $ text $ show loc
sh (StubExpr _ f es) = text f <>> tuple es
sh (IntrinsicExpr _ f es) = text (show $ externalFunctionName f) <>> tuple es
sh (ExtractExpr _ idx e) = shHighPrec e <<> brackets (int idx)
sh (StructExpr _ es) = braces <$> commas es
sh (UndefinedExpr) = return $ text "Undef"
sh (GEPExpr) = return $ text "GEP"
sh (IrrelevantExpr) = return $ text "IRRELEVANT"

bits :: ExprT -> Int
bits Int1T = 1
bits Int8T = 8
bits Int16T = 16
bits Int32T = 32
bits Int64T = 64
bits t = trace ("Unexpected argument to bits: " ++ show t) 64

repeatf :: (Eq a) => Int -> (a -> a) -> a -> a
repeatf 0 f x = trace "repeatf overflow. bailing." x
repeatf lim f x
    | fx == x = x
    | otherwise = repeatf (lim - 1) f fx
    where fx = f x

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
--simplify (ShlExpr t e1 (ILitExpr i))
--    | i >= 0 = simplify $ MulExpr t e1 (ILitExpr $ 2 ^ i)
simplify (ShlExpr t (ILitExpr a) (ILitExpr b))
    = ILitExpr $ (shiftL a $ fromIntegral b) `rem` (2 ^ bits t)
simplify (ShlExpr t e1 e2) = ShlExpr t (simplify e1) (simplify e2)
simplify (LshrExpr t (ILitExpr a) (ILitExpr b))
    = ILitExpr $ shiftR (a `rem` (2 ^ bits t)) $ fromIntegral b
simplify (LshrExpr t e1 e2) = LshrExpr t (simplify e1) (simplify e2)
simplify (AshrExpr _ (ILitExpr 0) _) = ILitExpr 0
simplify (AshrExpr t (ILitExpr a) (ILitExpr b))
    = ILitExpr $ case t of
        Int8T -> fromIntegral $ shiftR a8 $ fromIntegral b
        Int16T -> fromIntegral $ shiftR a16 $ fromIntegral b
        Int32T -> fromIntegral $ shiftR a32 $ fromIntegral b
        Int64T -> fromIntegral $ shiftR a64 $ fromIntegral b
    where a64 = (fromIntegral a) :: Word64
          a32 = (fromIntegral a) :: Word32
          a16 = (fromIntegral a) :: Word16
          a8 = (fromIntegral a) :: Word8
simplify (AshrExpr t e1 e2) = AshrExpr t (simplify e1) (simplify e2)
simplify (AndExpr t (ILitExpr a) (ILitExpr b)) = ILitExpr $ (a .&. b) `rem` (2 ^ bits t)
simplify (AndExpr _ (ZExtExpr _ e@(LoadExpr Int8T _ _)) (ILitExpr 255)) = simplify e
simplify (AndExpr Int32T e (ILitExpr 0xFFFFFFFF)) = simplify e
simplify (AndExpr Int64T e (ILitExpr 0xFFFFFFFF))
    = simplify $ ZExtExpr Int64T $ TruncExpr Int32T e
simplify (AndExpr t e1 e2) = AndExpr t (simplify e1) (simplify e2)
simplify
    (OrExpr t
        (LshrExpr _ e1 r@(ILitExpr a))
        (ShlExpr _ e2 l@(ILitExpr b)))
    | e1 == e2 && a + b == fromIntegral (bits t)
        = simplify $ case compare a b of
            LT -> StubExpr t "RotR" [e1, r]
            _ -> StubExpr t "RotL" [e2, l]
simplify
    (OrExpr t
        (ShlExpr _ e2 l@(ILitExpr b))
        (LshrExpr _ e1 r@(ILitExpr a)))
    | e1 == e2 && a + b == fromIntegral (bits t)
        = simplify $ case compare a b of
            LT -> StubExpr t "RotR" [e1, r]
            _ -> StubExpr t "RotL" [e2, l]
simplify
    (OrExpr t
        (ShlExpr _ e1 (ILitExpr 24))
        (OrExpr _
            (OrExpr _
                (LshrExpr _ e2 (ILitExpr 24))
                (AndExpr _
                    (LshrExpr _ e3 (ILitExpr 8))
                    (ILitExpr 0xFF00)))
            (AndExpr _
                (ShlExpr _ e4 (ILitExpr 8))
                (ILitExpr 0xFF0000))))
    | e1 == e2 && e2 == e3 && e3 == e4
        = simplify $ StubExpr t "Byteswap32" [e1]
simplify (OrExpr t (ILitExpr a) (ILitExpr b)) = ILitExpr $ (a .|. b) `rem` (2 ^ bits t)
simplify (OrExpr t e (ILitExpr 0)) = simplify e
simplify (OrExpr t (ILitExpr 0) e) = simplify e
simplify (OrExpr t e1 e2) = OrExpr t (simplify e1) (simplify e2)
simplify (XorExpr t (ILitExpr a) (ILitExpr b)) = ILitExpr $ (a `xor` b) `rem` (2 ^ bits t)
simplify (XorExpr t e1 e2) = XorExpr t (simplify e1) (simplify e2)
-- FIXME: HACK!!!!
--simplify (ZExtExpr _ e) = simplify e
--simplify (SExtExpr _ e) = simplify e
--simplify (TruncExpr _ e) = simplify e
simplify (TruncExpr t1 (TruncExpr t2 e))
    | bits t1 <= bits t2 = simplify $ TruncExpr t1 e
simplify (TruncExpr t1 (ZExtExpr t2 e))
    | t1 == t2 = simplify e
    | bits t1 < bits t2 = simplify $ TruncExpr t1 e
simplify (TruncExpr t1 (SExtExpr t2 e))
    | t1 == t2 = simplify e
    | bits t1 < bits t2 = simplify $ TruncExpr t1 e
simplify expr@(TruncExpr t e@(ILitExpr int))
    | int < 2 ^ bits t = e
    | otherwise = expr
simplify (TruncExpr t e) = simplify e
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
simplify (ICmpExpr ICmpEq (ILitExpr a) (ILitExpr b))
    | a == b = ILitExpr 1
    | otherwise = ILitExpr 0
simplify (ICmpExpr p e1 e2) = ICmpExpr p (simplify e1) (simplify e2)
simplify (ExtractExpr t 0 (IntrinsicExpr _ f [e1, e2]))
    | "llvm.uadd.with.overflow" `L.isPrefixOf`
        identifierAsString (externalFunctionName f)
        = simplify $ AddExpr t e1 e2
simplify (ExtractExpr _ 1 (IntrinsicExpr (StructT [_, t])
             f [ILitExpr a, ILitExpr b]))
    | "llvm.uadd.with.overflow" `L.isPrefixOf`
        identifierAsString (externalFunctionName f)
        = case compare (a + b) (2 ^ bits t) of
            LT -> ILitExpr 0
            _ -> ILitExpr 1
simplify (StubExpr t f es) = StubExpr t f $ map simplify es
simplify (IntrinsicExpr t f es) = IntrinsicExpr t f $ map simplify es
simplify (ExtractExpr _ idx (StructExpr _ es)) = simplify $ es !! idx
simplify (ExtractExpr t idx e) = ExtractExpr t idx (simplify e)
simplify (StructExpr t es) = StructExpr t $ map simplify es
simplify e = e

-- Simple type system
typeToExprT :: Type -> ExprT
typeToExprT (TypeInteger 1) = Int1T
typeToExprT (TypeInteger 8) = Int8T
typeToExprT (TypeInteger 16) = Int16T
typeToExprT (TypeInteger 32) = Int32T
typeToExprT (TypeInteger 64) = Int32T
typeToExprT (TypePointer _ _) = PtrT
typeToExprT (TypeFloat) = FloatT
typeToExprT (TypeDouble) = DoubleT
typeToExprT (TypeStruct _ ts _) = StructT $ map typeToExprT ts
typeToExprT t = trace (printf "making VoidT from %s" (show t)) VoidT

exprTOfInst :: Instruction -> ExprT
exprTOfInst = typeToExprT . instructionType
