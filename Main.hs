{-# LANGUAGE StandaloneDeriving, OverloadedStrings #-}
module Main where

import Data.LLVM.Types
import LLVM.Parse

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Control.Monad.Trans.Maybe
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
import qualified Data.Text.IO as TIO

import Data.RESET.Types
import Eval
import Expr
import Memlog
import Options

deriving instance Show Command
deriving instance Show Response

type SymbReader = ReaderT SymbolicState IO

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
    [ Option [] ["debug-ip"]
        (ReqArg (\a o -> o{ optDebugIP = Just $ read a }) "Need IP")
        "Run in debug mode on a given IP; write out trace at that IP."
    , Option ['q'] ["qemu-dir"]
        (ReqArg (\a o -> o{ optQemuDir = Just a }) "Need dir")
        "Run QEMU on specified program."
    , Option ['t'] ["qemu-target"]
        (ReqArg (\a o -> o{ optQemuTarget = a }) "Need triple")
        "Run specified QEMU target. Default i386-linux-user."
    , Option ['d'] ["log-dir"]
        (ReqArg (\a o -> o{ optLogDir = a }) "Need dir")
        "Place or look for QEMU LLVM logs in a given dir."
    ]

runQemu :: String -> String -> String -> [String] -> IO ()
runQemu dir target logdir prog = do
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
    let dirArgs = if logdir == "/tmp" then []
            else ["-panda-arg", "llvm_trace:base=" ++ logdir]
    let qemuArgs = ["-panda-plugin", plugin] ++ dirArgs ++ progShifted
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
        Just dir -> runQemu dir (optQemuTarget options) (optLogDir options)
            nonOptions
        Nothing -> return ()

    -- The goal here is to postpone all computation as much as possible, so
    -- that everything is captured by the progress meter in the main execState.

    -- Load LLVM files and dynamic logs
    let llvmMod = optLogDir options </> "llvm-mod.bc"
    let functionLog = optLogDir options </> "llvm-functions.log"
    printf "Loading LLVM module from %s.\n" llvmMod
    theMod <- parseLLVMFile defaultParserOptions llvmMod
    seq theMod $ printf "Parsing execution log from %s.\n" functionLog
    funcNameList <- T.lines <$> TIO.readFile functionLog
    let funcMap = MS.fromList $
            map (\f -> (identifierContent $ functionName f, f)) $
                moduleDefinedFunctions theMod
        findFunc name = fromMaybe (error $ "Couldn't find function " ++ T.unpack name) $ MS.lookup name funcMap
        funcList = map findFunc funcNameList
        funcCount = length $ funcNameList

    -- Align dynamic log with execution history
    putStrLn "Loading dynamic log."
    memlog <- parseMemlog $ optLogDir options </> "llvm-memlog.log"
    putStr "Aligning dynamic log data..."
    let associated = associateFuncs memlog funcList
    putStrLn $
        printf " done.\nRunning symbolic execution analysis with %d functions."
            funcCount

    -- Run symbolic execution analysis
    let initialState = noSymbolicState{
        symbolicTotalFuncs = funcCount,
        symbolicOptions = options
    }
    let state = execState (runMaybeT $ runBlocks associated) initialState
    seq state $ putStrLn ""
    unless (null $ warnings state) $ do
        putStrLn "Warnings:"
        putStrLn $ L.intercalate "\n" $ map showWarning $ warnings state

    -- Serve requests for data from analysis
    let addr = PortNumber 22022
    sock <- listenOn addr
    putStrLn $ printf "Listening on %s." (show addr)
    forever $ catchIOError (accept sock >>= process state) $ \e -> print e
