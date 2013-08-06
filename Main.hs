{-# LANGUAGE StandaloneDeriving, OverloadedStrings #-}
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
import System.Console.GetOpt
import System.Cmd(rawSystem)
import System.Directory(setCurrentDirectory, canonicalizePath)
import System.Environment(getArgs)
import System.Exit(ExitCode(..), exitFailure)
import System.FilePath((</>))
import System.IO
import System.IO.Error
import Text.Printf

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import qualified Data.Text as T

import Data.RESET.Types
import Eval
import Expr
import Memlog
import Options
import Progress

deriving instance Show Command
deriving instance Show Response

type SymbReader = ReaderT SymbolicState IO

interesting :: String -> [Function] -> Interesting
interesting focus fs = (before, reverse revOurs, reverse revAfter)
    where boring = not . L.isInfixOf focus . identifierAsString . functionName
          (before, afterFirst) = span boring fs
          revAfterFirst = reverse afterFirst
          (revAfter, revOurs) = span boring revAfterFirst

processCmd :: SymbolicState -> String -> IO Response
processCmd state s = case parseCmd s of
    Left err -> do
        putStrLn $ printf "Parse error on %s:\n  %s" (show s) err
        return $ ErrorResponse err
    Right cmd -> do
        putStrLn $ printf "executing command: %s" (show cmd)
        runReaderT (respond cmd) state
    where parseCmd = eitherDecode . BS.pack :: String -> Either String Command

respond :: Command -> SymbReader Response
respond WatchIP{ commandIP = ip,
                 commandLimit = limit,
                 commandExprOptions = opts }
    = MessagesResponse <$> map (messageMap $ renderExpr opts) <$>
        take limit <$> asks (messagesByIP ip)

process :: SymbolicState -> (Handle, HostName, PortNumber) -> IO ()
process state (handle, _, _) = do
    putStrLn "Client connected."
    commands <- lines <$> hGetContents handle
    mapM_ (BS.hPutStrLn handle <=< liftM encode . processCmd state) commands

-- Command line arguments
opts :: [OptDescr (Options -> Options)]
opts =
    [ Option ['d'] ["debug-ip"]
        (ReqArg (\a o -> o{ optDebugIP = Just $ read a }) "Need IP")
        "Run in debug mode on a given IP; write out trace at that IP."
    , Option ['q'] ["qemu-dir"]
        (ReqArg (\a o -> o{ optQemuDir = Just a }) "Need dir")
        "Run QEMU on specified program."
    , Option ['t'] ["qemu-target"]
        (ReqArg (\a o -> o{ optQemuTarget = a }) "Need triple")
        "Run specified QEMU target. Default i386-linux-user."
    ]

runQemu :: String -> String -> [String] -> IO ()
runQemu dir target prog = do
    arch <- case map T.unpack $ T.splitOn "-" (T.pack target) of
        [arch, _, _] -> return arch
        _ -> putStrLn "Bad target triple." >> exitFailure
    -- Make sure we run prog relative to old working dir.
    progShifted <- case prog of
        progName : progArgs -> do
            progPath <- canonicalizePath progName
            return $ progPath : progArgs
        _ -> return $ error "Need a program to run."
    -- We HAVE to be in the QEMU dir to run successfully; location of helper
    -- function bitcode requires it.
    putStrLn $ printf "Switching to directory %s." dir
    setCurrentDirectory dir
    let qemu = target </> printf "qemu-%s" arch
    let plugin = target </> "panda_plugins" </> "panda_llvm_trace.so"
    let qemuArgs = ["-panda-plugin", plugin] ++ progShifted
    putStrLn $ printf "Running QEMU at %s with args %s..." qemu (show qemuArgs)
    exitCode <- rawSystem qemu qemuArgs
    case exitCode of
        ExitFailure code ->
            putStrLn $ printf "\nQEMU exited with return code %d." code
        ExitSuccess -> putStrLn "Done running QEMU."

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering
    args <- getArgs
    let (optionFs, nonOptions, optionErrs) = getOpt RequireOrder opts args
    case optionErrs of
        [] -> return ()
        _ -> mapM putStrLn optionErrs >> exitFailure
    let options = foldl (flip ($)) defaultOptions optionFs

    -- Run QEMU if necessary
    case optQemuDir options of
        Just dir -> runQemu dir (optQemuTarget options) nonOptions
        Nothing -> return ()

    -- Load LLVM files and dynamic logs
    putStrLn "Loading LLVM module from /tmp/llvm-mod.bc."
    theMod <- parseLLVMFile defaultParserOptions "/tmp/llvm-mod.bc"
    seq theMod $ putStrLn "Parsing execution log."
    funcNameList <- lines <$> readFile "/tmp/llvm-functions.log"
    let findFunc name = fromMaybe (error $ "Couldn't find function " ++ name) $ findFunctionByName theMod name
    let funcList = map findFunc funcNameList
    let interestingFuncs = interesting "main" funcList

    -- Align dynamic log with execution history
    seq interestingFuncs $ putStrLn "Loading dynamic log."
    memlog <- parseMemlog
    seq memlog $ putStr "Aligning dynamic log data..."
    let associated = associateFuncs memlog interestingFuncs
    let instructionCount = numInstructions associated
    seq associated $ putStrLn $
        printf " done.\nRunning symbolic execution analysis with %d instructions."
            instructionCount

    -- Run symbolic execution analysis
    let initialState = noSymbolicState{
        symbolicTotalInstructions = instructionCount,
        symbolicOptions = options
    }
    let (result, state) = runState (runProgressT $ runBlocks associated) initialState
    showProgress result
    seq state $ unless (null $ warnings state) $ do
        putStrLn "Warnings:"
        putStrLn $ L.intercalate "\n" $ map showWarning $ warnings state

    -- Serve requests for data from analysis
    let addr = PortNumber 22022
    sock <- listenOn addr
    putStrLn $ printf "Listening on %s." (show addr)
    forever $ catchIOError (accept sock >>= process state) $ \e -> print e
