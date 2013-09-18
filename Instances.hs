{-# LANGUAGE StandaloneDeriving, DeriveGeneric, DefaultSignatures #-}
module Instances where

import Control.Applicative((<$>))
import Data.LLVM.Types
import Data.Serialize
import Data.Text(Text)
import Data.Vector(Vector, fromList, toList)
import GHC.Generics

import qualified Data.Text.Encoding as TE

deriving instance Show Constant
deriving instance Show ExternalValue
deriving instance Show GlobalAlias

deriving instance Ord CmpPredicate

deriving instance Generic GlobalAlias
instance Serialize GlobalAlias where

deriving instance Generic ExternalFunction
instance Serialize ExternalFunction where

deriving instance Generic Type
instance Serialize Type where

deriving instance Generic DW_ATE
instance Serialize DW_ATE where

deriving instance Generic DW_TAG
instance Serialize DW_TAG where

deriving instance Generic Metadata
instance Serialize Metadata where

deriving instance Generic Module
instance Serialize Module where

deriving instance Generic VisibilityStyle
instance Serialize VisibilityStyle where

deriving instance Generic FunctionAttribute
instance Serialize FunctionAttribute where

deriving instance Generic DW_VIRTUALITY
instance Serialize DW_VIRTUALITY where

deriving instance Generic ExternalValue
instance Serialize ExternalValue where

deriving instance Generic LinkageType
instance Serialize LinkageType where

deriving instance Generic DW_LANG
instance Serialize DW_LANG where

deriving instance Generic GlobalVariable
instance Serialize GlobalVariable where

deriving instance Generic Identifier
instance Serialize Identifier where

deriving instance Generic Function
instance Serialize Function where

deriving instance Generic Value
instance Serialize Value where

instance Serialize Text where
    put = put . TE.encodeUtf8
    get = TE.decodeUtf8 <$> get

deriving instance Generic Assembly
instance Serialize Assembly where

deriving instance Generic ParamAttribute
instance Serialize ParamAttribute where

deriving instance Generic Constant
instance Serialize Constant where

deriving instance Generic DataLayout
instance Serialize DataLayout where

deriving instance Generic CallingConvention
instance Serialize CallingConvention where

deriving instance Generic Argument
instance Serialize Argument where

deriving instance Generic Instruction
instance Serialize Instruction where

instance Serialize a => Serialize (Vector a) where
    put = put . toList
    get = fromList <$> get

deriving instance Generic BasicBlock
instance Serialize BasicBlock where

deriving instance Generic AlignmentPref
instance Serialize AlignmentPref where

deriving instance Generic LandingPadClause
instance Serialize LandingPadClause where

deriving instance Generic Endianness
instance Serialize Endianness where

deriving instance Generic CmpPredicate
instance Serialize CmpPredicate where

deriving instance Generic ArithFlags
instance Serialize ArithFlags where

deriving instance Generic AtomicOperation
instance Serialize AtomicOperation where

deriving instance Generic SynchronizationScope
instance Serialize SynchronizationScope where

deriving instance Generic AtomicOrdering
instance Serialize AtomicOrdering where
