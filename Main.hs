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
import System.Process(runProcess, waitForProcess)
import System.Directory(setCurrentDirectory, canonicalizePath)
import System.Environment(getArgs)
import System.Exit(ExitCode(..), exitFailure)
import System.FilePath((</>))
import System.IO
import System.IO.Error
import Text.Printf

import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BSL
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE

import Data.RESET.Types
import Eval
import Expr
import Memlog
import Options

deriving instance Show Command
deriving instance Show Response

type SymbReader = ReaderT SymbolicState IO

processCmd :: String -> IO Response
processCmd s = case parseCmd s of
    Left err -> do
        putStrLn $ printf "Parse error on %s:\n  %s" (show s) err
        return $ ErrorResponse err
    Right cmd -> do
        putStrLn $ printf "executing command: %s" (show cmd)
        respond cmd
    where parseCmd = eitherDecode . BSL.pack :: String -> Either String Command

respond :: Command -> IO Response
respond WatchIP{ commandIP = ip,
                 commandLimit = limit,
                 commandExprOptions = opts }
    = MessagesResponse <$> map (messageMap $ renderExpr opts) <$>
        take limit <$> messagesByIP ip <$> (parseOptions >>= symbolic ip)

process :: (Handle, HostName, PortNumber) -> IO ()
process (handle, _, _) = do
    putStrLn "Client connected."
    commands <- lines <$> hGetContents handle
    mapM_ (BSL.hPutStrLn handle <=< liftM encode . processCmd) commands

-- Command line arguments
opts :: [OptDescr (Options -> Options)]
opts =
    [ Option [] ["debug-ip"]
        (ReqArg (\a o -> o{ optDebugIP = Just $ read a }) "Need IP")
        "Run in debug mode on a given IP; write out trace at that IP."
    , Option ['q'] ["qemu-dir"]
        (ReqArg (\a o -> o{ optQemuDir = a }) "Need dir")
        "Run QEMU on specified program."
    , Option ['t'] ["qemu-target"]
        (ReqArg (\a o -> o{ optQemuTarget = a }) "Need triple") $
        "Run specified QEMU target. Default i386-linux-user for user mode " ++
        "and i386-softmmu for whole-system mode."
    , Option ['c'] ["qemu-cr3"]
        (ReqArg (\a o -> o{ optQemuCr3 = Just $ read a }) "Need CR3")
        "Run QEMU with filtering on a given CR3 (in whole-system mode)."
    , Option ['r'] ["qemu-replay"]
        (ReqArg (\a o -> o{ optQemuReplay = Just a }) "Need replay")
        "Run specified replay in QEMU (exclude filename extension)."
    , Option [] ["qemu-qcows"]
        (ReqArg (\a o -> o{ optQemuQcows = Just a }) "Need qcows")
        "Use specified Qcows2 with QEMU."
    , Option ['d'] ["log-dir"]
        (ReqArg (\a o -> o{ optLogDir = a }) "Need dir")
        "Place or look for QEMU LLVM logs in a given dir."
    ]

data WholeSystemArgs = WSA
    { wsaCr3 :: Word64
    , wsaReplay :: FilePath
    , wsaQcows :: FilePath
    , wsaTrigger :: Word64
    }

getWSA :: Options -> Maybe WholeSystemArgs
getWSA Options{ optQemuCr3 = Just cr3,
                optQemuReplay = Just replay, 
                optQemuQcows = Just qcows }
    = Just $ WSA{ wsaCr3 = cr3, wsaReplay = replay, wsaQcows = qcows,
        wsaTrigger = error "Trigger not initialized" }
getWSA _ = Nothing

runQemu :: FilePath -> String -> FilePath -> Maybe WholeSystemArgs -> [String] -> IO ()
runQemu dir target logdir wsArgs prog = do
    arch <- case map T.unpack $ T.splitOn "-" (T.pack target) of
        [arch, _, _] -> return arch
        [arch, "softmmu"] -> return arch
        _ -> putStrLn "Bad target triple." >> exitFailure
    -- Make sure we run prog relative to old working dir.
    progShifted <- case prog of
        progName : progArgs -> do
            progPath <- canonicalizePath progName
            return $ progPath : progArgs
        _ -> return $ error "Need a program to run."
    let qemu = dir </> target </> 
            if isJust wsArgs -- if in whole-system mode
                then printf "qemu-system-%s" arch
                else printf "qemu-%s" arch
        otherArgs = ["-tubtf", "-monitor", "tcp:localhost:4444,server,nowait"]
        plugin = target </> "panda_plugins" </> "panda_llvm_trace.so"
        pluginArgs =
            ["-panda-plugin", plugin,
             "-panda-arg", "llvm_trace:base=" ++ logdir]
        runArgs = case wsArgs of
            Nothing -> progShifted -- user mode
            Just (WSA cr3 replay qcows trigger) -> -- whole-system mode
                ["-m", "2048", qcows, "-replay", replay,
                 "-panda-arg", printf "llvm_trace:cr3=%x" cr3,
                 "-panda-arg", printf "llvm_trace:trigger=%x" trigger]
        qemuArgs = otherArgs ++ pluginArgs ++ runArgs
    putStrLn $ printf "Running QEMU at %s with args %s..." qemu (show qemuArgs)
    -- Don't pass an environment, and use our stdin/stdout
    proc <- runProcess qemu qemuArgs (Just dir) Nothing Nothing Nothing Nothing
    exitCode <- waitForProcess proc
    case exitCode of
        ExitFailure code ->
            putStrLn $ printf "\nQEMU exited with return code %d." code
        ExitSuccess -> putStrLn "Done running QEMU."

-- Run a round of symbolic evaluation
symbolic :: Word64 -> (Options, [String]) -> IO SymbolicState
symbolic trigger (options, nonOptions) = do
    let logDir = optLogDir options
        dir = optQemuDir options

    -- Run QEMU if necessary
    case getWSA options of
        Just wsa ->
            runQemu dir (optQemuTarget options) logDir
                (Just wsa{ wsaTrigger = trigger }) nonOptions
        Nothing ->
            runQemu dir (optQemuTarget options) logDir
                Nothing nonOptions

    -- Load LLVM files and dynamic logs
    let llvmMod = logDir </> "llvm-mod.bc"
    printf "Loading LLVM module from %s.\n" llvmMod
    theMod <- parseLLVMFile defaultParserOptions llvmMod

    -- Align dynamic log with execution history
    putStrLn "Loading dynamic log."
    memlog <- parseMemlog $ optLogDir options </> "tubtf.log"
    putStr "Aligning dynamic log data..."
    let associated = associateFuncs memlog theMod
    putStrLn $
        printf " done.\nRunning symbolic execution analysis with FIXME functions."

    -- Run symbolic execution analysis
    let initialState = noSymbolicState{
        symbolicTotalFuncs = 1000000000, -- FIXME
        symbolicOptions = options
    }
    let (_, state) = runState (runBlocks associated) initialState
    seq state $ return state

parseOptions :: IO (Options, [String])
parseOptions = do
    args <- getArgs
    let (optionFs, nonOptions, optionErrs) = getOpt RequireOrder opts args
    case optionErrs of
        [] -> return ()
        _ -> mapM putStrLn optionErrs >> exitFailure
    return $ (foldl (flip ($)) defaultOptions optionFs, nonOptions)

main :: IO ()
main = do
    hSetBuffering stdout NoBuffering

    -- Serve requests for data from analysis
    let addr = PortNumber 22022
    sock <- listenOn addr
    putStrLn $ printf "Listening on %s." (show addr)
    forever $ catchIOError (accept sock >>= process) $ \e -> print e
