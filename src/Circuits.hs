{-@ LIQUID "--reflection" @-}
module Circuits where

import Constraints

{-@ reflect emptyCircuit @-}
{-@ emptyCircuit :: m:Nat -> Circuit p 0 m @-}
emptyCircuit :: Int -> Circuit p
emptyCircuit _ = []

{-@ reflect constGate @-}
{-@ constGate :: m:Nat -> p -> Btwn 0 m -> Circuit p 1 m @-}
constGate :: Num p => Int -> p -> Int -> Circuit p
constGate _ x n = [(v, q)] where
  v = [0, 0, n]
  q = [0, 0, -1, 0, x]
  -- the output wire ‘n’ contains the value ‘x’
  -- the input wires are not used
