{-# LANGUAGE StandaloneDeriving #-}
module Main where

import Data.LLVM.Types
import LLVM.Parse

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.Aeson
import Data.Maybe
import Data.Word
import Debug.Trace
import Network
import System.IO
import Text.Printf

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Text as T

import Data.RESET.Types
import Eval
import Memlog

deriving instance Show Command
deriving instance Show Response

type SymbReader = Reader SymbolicState

interesting :: String -> [Function] -> Interesting
interesting focus fs = (before, reverse revOurs, reverse revAfter)
    where boring = not . L.isInfixOf focus . identifierAsString . functionName
          (before, afterFirst) = span boring fs
          revAfterFirst = reverse afterFirst
          (revAfter, revOurs) = span boring revAfterFirst

processCmd :: SymbolicState -> String -> IO Response
processCmd state s = case parseCmd s of
    Left err -> do
        putStrLn $ printf "Parse error: %s" err
        return $ ErrorResponse err
    Right cmd -> do
        putStrLn $ printf "executing command: %s" (show cmd)
        return $ runReader (respond cmd) state
    where parseCmd = eitherDecode . BS.pack :: String -> Either String Command

respond :: Command -> SymbReader Response
respond WatchIP{ commandIP = ip, commandLimit = limit }
    = MessagesResponse <$> take limit <$> asks (messagesByIP ip)

process :: SymbolicState -> (Handle, HostName, PortNumber) -> IO ()
process state (handle, _, _) = do
    hPutStrLn handle "connected"
    commands <- lines <$> hGetContents handle
    mapM_ (hPutStrLn handle <=< liftM show . processCmd state) commands

main :: IO ()
main = do
    theMod <- parseLLVMFile defaultParserOptions "/tmp/llvm-mod.bc"
    funcNameList <- lines <$> readFile "/tmp/llvm-functions.log"
    let findFunc name = fromMaybe (error $ "Couldn't find function " ++ name) $ findFunctionByName theMod name
    let funcList = map findFunc funcNameList
    let interestingFuncs = interesting "main" funcList
    memlog <- parseMemlog
    putStrLn "Aligning dynamic log data"
    let associated = associateFuncs memlog interestingFuncs
    seq associated $ putStrLn "Running symbolic execution analysis"
    let state = execState (unSymbolic $ runBlocks associated) noSymbolicState
    print $ symbolicWarnings state
    let addr = UnixSocket "/tmp/reset.sock"
    sock <- listenOn addr
    putStrLn $ printf "Listening on %s" (show addr)
    accept sock >>= process state
