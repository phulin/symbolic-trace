{-# LANGUAGE StandaloneDeriving #-}
module Data.RESET.Expr where

import Data.LLVM.Types
import Text.Printf

import Data.RESET.Memlog

deriving instance Ord CmpPredicate

data Loc = IdLoc Identifier Identifier | MemLoc AddrEntry
    deriving (Eq, Ord)

data ExprT = VoidT | PtrT | Int1T | Int8T | Int32T | Int64T | FloatT | DoubleT
    | StructT [ExprT]
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
    -- Type, dynamic address, and name.
    LoadExpr ExprT AddrEntry (Maybe String) |
    ICmpExpr CmpPredicate Expr Expr |
    ILitExpr Integer | -- takes any integer type
    FLitExpr Double | -- takes any float type
    InputExpr ExprT Loc |
    StubExpr ExprT String [Expr] |
    IntrinsicExpr ExprT ExternalFunction [Expr] |
    ExtractExpr ExprT Int Expr |
    GEPExpr | -- dummy expression for getelementptr instructions
    IrrelevantExpr
    deriving (Eq, Ord)
