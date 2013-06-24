module Options(Options(..), defaultOptions) where

data Options = Options
    { optDebug :: Bool
    } deriving Show

defaultOptions :: Options
defaultOptions = Options
    { optDebug = False
    }
