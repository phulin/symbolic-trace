module Options(Options(..), defaultOptions) where

import Data.Word(Word64)

data Options = Options
    { optDebugIP :: Maybe Word64
    } deriving Show

defaultOptions :: Options
defaultOptions = Options
    { optDebugIP = Nothing
    }
