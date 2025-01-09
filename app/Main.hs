{-@ LIQUID "--reflection" @-}
module Main (main) where

import Examples
import DSL

main :: IO ()
main = do
  -- testArithmetic
  -- testBoolean
  -- testLoops
  testVectors
  testMod
  testSha
  testOpt
