module Options(Options(..), defaultOptions) where

import Data.Word(Word64)

data Options = Options
    { optDebugIP :: Maybe Word64
    , optQemuDir :: Maybe String
    , optQemuTarget :: String
    } deriving Show

defaultOptions :: Options
defaultOptions = Options
    { optDebugIP = Nothing
    , optQemuDir = Nothing
    , optQemuTarget = "i386-linux-user"
    }
