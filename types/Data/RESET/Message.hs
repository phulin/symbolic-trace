{-# LANGUAGE TemplateHaskell #-}
module Data.RESET.Message where

import Data.Aeson
import Data.Aeson.TH
import Data.LLVM.Types
import Data.Word

import Data.RESET.Memlog
import Data.RESET.Expr

data Command =
    WatchIP{ commandIP :: Word64,
             commandLimit :: Int }
    deriving (Eq, Ord)

data Response =
    ErrorResponse{ responseError :: String } |
    MessagesResponse{ responseMessages :: [Message] }
    deriving (Eq, Ord)

data Message =
    MemoryMessage{ messageOp :: AddrOp,
                   messageAddr :: AddrEntry,
                   messageExpr :: Expr,
                   messageOrigin :: Maybe Expr } |
    BranchMessage{ messageExpr :: Expr,
                   messageTaken :: Bool } |
    UnconditionalBranchMessage |
    WarningMessage{ messageWarning :: String }
    deriving (Eq, Ord)

$(deriveJSON id ''DW_TAG)
$(deriveJSON id ''DW_ATE)
$(deriveJSON id ''DW_VIRTUALITY)
$(deriveJSON id ''DW_LANG)
$(deriveJSON id ''FunctionAttribute)
$(deriveJSON id ''Metadata)
$(deriveJSON id ''Identifier)
$(deriveJSON id ''Type)
$(deriveJSON id ''Loc)
$(deriveJSON id ''CmpPredicate)
$(deriveJSON id ''ExprT)
$(deriveJSON id ''ExternalFunction)
$(deriveJSON id ''AddrFlag)
$(deriveJSON id ''AddrEntryType)
$(deriveJSON id ''Expr)
$(deriveJSON id ''AddrEntry)
$(deriveJSON id ''AddrOp)
$(deriveJSON (drop 7) ''Message)
$(deriveJSON (drop 7) ''Command)
$(deriveJSON (drop 8) ''Response)
