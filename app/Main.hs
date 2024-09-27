{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Main (main) where

import Examples

main :: IO ()
main = do
  testArithmetic
  testBoolean
  testLoops
  testVectors
