module Main where

import Data.LLVM.Types
import LLVM.Parse

import Data.Maybe
import Control.Applicative
import Control.Monad
import Control.Monad.State.Lazy

import qualified Data.List as L

import Eval
import Memlog

interesting :: String -> [Function] -> Interesting
interesting focus fs = (before, reverse revOurs, reverse revAfter)
    where boring = not . L.isInfixOf focus . identifierAsString . functionName
          (before, afterFirst) = span boring fs
          revAfterFirst = reverse afterFirst
          (revAfter, revOurs) = span boring revAfterFirst

main :: IO ()
main = do
    theMod <- parseLLVMFile defaultParserOptions "/tmp/llvm-mod.bc"
    funcNameList <- lines <$> readFile "/tmp/llvm-functions.log"
    let findFunc name = fromMaybe (error $ "Couldn't find function " ++ name) $ findFunctionByName theMod name
    let funcList = map findFunc funcNameList
    let interestingFuncs = interesting "sub_" funcList
    memlog <- parseMemlog
    let associated = associateFuncs memlog interestingFuncs
    -- putStrLn $ showAssociated associated
    let state = execState (unSymbolic $ runBlocks associated) noSymbolicState
    let warnings = symbolicWarnings $ state
    let messages = symbolicMessages $ state
    -- when (not $ null warnings) $ do
    --     putStrLn "Warnings:"
    --     putStrLn $ L.intercalate "\n" $ map showWarning warnings
    --     putStrLn ""
    when (not $ null messages) $ do
        putStrLn "Messages:"
        putStrLn $ L.intercalate "\n" messages
        putStrLn ""
