{-@ embed GHC.Num.Natural.Natural as int @-}
{-@ LIQUID "--reflection" @-}
{-# LANGUAGE DataKinds #-}
module Main (main) where

import Data.FiniteField.PrimeField
import Vec
import Utils (allRange)
import ArithmeticGates
import LogicGates
import Constraints

main :: IO ()
main = do

  print $ satisfies 1 3 (fromList [2,3,5] :: Vec (PrimeField 17)) addGate -- True
  print $ satisfies 1 3 (fromList [2,3,6] :: Vec (PrimeField 17)) addGate -- False
  print $ satisfies 1 3 (fromList [5,3,10] :: Vec (PrimeField 17)) mulGate -- False
  print $ satisfies 1 3 (fromList [5,3,-2] :: Vec (PrimeField 17)) mulGate -- True
  putStrLn ""
  print $ satisfies 3 3 (fromList [0, 1, 1] :: Vec (PrimeField 17)) orGate -- True
  print $ satisfies 2 2 (fromList [2, 0] :: Vec (PrimeField 17)) notGate   -- False
