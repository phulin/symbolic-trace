module Options(Options(..), defaultOptions) where

import Data.Word(Word64)

data Options = Options
    { optDebugIP :: Maybe Word64
    , optQemuDir :: FilePath
    , optQemuTarget :: String
    , optQemuCr3 :: Maybe Word64
    , optQemuReplay :: Maybe FilePath
    , optQemuQcows :: Maybe FilePath
    , optLogDir :: FilePath
    } deriving Show

defaultOptions :: Options
defaultOptions = Options
    { optDebugIP = Nothing
    , optQemuDir = "."
    , optQemuTarget = "i386-linux-user"
    , optQemuCr3 = Nothing
    , optQemuReplay = Nothing
    , optQemuQcows = Nothing
    , optLogDir = "/tmp"
    }
