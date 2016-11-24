module Main where

import qualified System.Environment
import qualified Compiler.Llvm as Comp


main :: IO ()
main = interact Comp.testCompile
