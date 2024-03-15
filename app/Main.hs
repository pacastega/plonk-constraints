{-@ embed GHC.Num.Natural.Natural as int @-}
{-@ LIQUID "--reflection" @-}
{-# LANGUAGE DataKinds #-}
module Main (main) where

import Data.FiniteField.PrimeField
import Vec
import Utils (allRange) -- needed to use ‘satisfies’ in the reflection
import ArithmeticGates
import LogicGates
import Constraints

import DSL

type V17 = Vec (PrimeField 17)

{-@ circ1 :: DSL _ (Btwn Int 0 10) @-}
circ1 :: DSL 17 Int
circ1 = MUL (ADD (WIRE 0) (CONST 15)) (ADD (WIRE 1) (CONST 3))

main :: IO ()
main = do

  print $ satisfies 1 3 (fromList [2,3,5] :: V17) (addGate 3 [0,1,2])  -- True
  print $ satisfies 1 3 (fromList [2,3,6] :: V17) (addGate 3 [0,1,2])  -- False
  print $ satisfies 1 3 (fromList [5,3,10] :: V17) (mulGate 3 [0,1,2]) -- False
  print $ satisfies 1 3 (fromList [5,3,-2] :: V17) (mulGate 3 [0,1,2]) -- True
  putStrLn ""
  print $ satisfies 3 3 (fromList [0, 1, 1] :: V17) orGate -- True
  print $ satisfies 2 2 (fromList [2, 0] :: V17) notGate   -- False
  putStrLn ""

  print $ compile 10 circ1
  -- print $ compile 10 (MUL (WIRE 0) (ADD (WIRE 1) (CONST 3)) :: DSL 17)
  -- print $ compile 10 (MUL (WIRE 0) (ADD (WIRE 1) (WIRE 3)) :: DSL 17)
