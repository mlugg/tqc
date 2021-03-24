{-# LANGUAGE DataKinds, OverloadedStrings, LambdaCase #-}

module Main where

import Cli
import Tqc

compilerMain :: Tqc ()
compilerMain = pure ()

main :: IO ()
main = parseArgs >>= \ case
  Nothing -> pure ()
  Just cfg -> runTqc compilerMain cfg >>= \ case
    Left _ -> _
    Right () -> putStrLn "Compilation successful!"
