
module Main where

import LexLintte
import ParLintte
import AbsLintte
import Interpreter
import TypeChecker

import ErrM

main = do
    x <- getContents
    calc x

calc :: String -> IO ()
calc s =
  let e = pProgram (myLexer s)
    in case e of
        Ok e' -> typeCheck e' >> interpret e'
        Bad e' -> print e'
