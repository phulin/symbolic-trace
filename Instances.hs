{-# LANGUAGE StandaloneDeriving #-}
module Instances where

import Data.LLVM.Types

deriving instance Show Constant
deriving instance Show ExternalValue
deriving instance Show GlobalAlias
deriving instance Show GlobalVariable
deriving instance Show BasicBlock
deriving instance Show ValueContent
