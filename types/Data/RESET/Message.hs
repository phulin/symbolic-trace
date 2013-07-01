{-# LANGUAGE TemplateHaskell #-}
module Data.RESET.Message where

import Data.Aeson
import Data.Aeson.TH
import Data.Functor
import Data.LLVM.Types
import Data.Word
import System.Exit(ExitCode(..))

import Data.RESET.Memlog
import Data.RESET.Expr

data Command =
    WatchIP{ commandIP :: Word64,
             commandLimit :: Int }
    deriving (Eq, Ord)

data Response =
    ErrorResponse{ responseError :: String } |
    MessagesResponse{ responseMessages :: [Message String] } |
    ExitCodeResponse{ responseExitCode :: ExitCode }
    deriving (Eq, Ord)

-- Parameterized over whether to represent symbolic expressions as Exprs
-- or as Strings.
data Message a =
    MemoryMessage{ messageOp :: AddrOp,
                   messageAddr :: String,
                   messageExpr :: a,
                   messageOrigin :: Maybe a } |
    BranchMessage{ messageExpr :: a,
                   messageTaken :: Bool } |
    UnconditionalBranchMessage |
    WarningMessage{ messageWarning :: String }
    deriving (Eq, Ord)

messageMap :: (a -> b) -> Message a -> Message b
messageMap f (MemoryMessage op addr expr origin)
    = MemoryMessage op addr (f expr) (f `fmap` origin)
messageMap f (BranchMessage expr taken)
    = BranchMessage (f expr) taken
messageMap _ UnconditionalBranchMessage = UnconditionalBranchMessage
messageMap _ (WarningMessage w) = WarningMessage w

$(deriveJSON id ''ExitCode)
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
