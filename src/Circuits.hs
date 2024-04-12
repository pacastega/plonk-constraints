{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed GHC.Num.Natural.Natural as int @-}
module Circuits where

import Constraints
import GHC.TypeNats (KnownNat)
import Vec
import Utils (zipWith')

{-@ reflect emptyCircuit @-}
{-@ emptyCircuit :: m:Nat -> Circuit (F p) 0 m @-}
emptyCircuit :: Int -> Circuit (F p)
emptyCircuit _ = []

{-@ reflect constGate @-}
{-@ constGate :: m:Nat -> F p -> Btwn Int 0 m -> Circuit (F p) 1 m @-}
constGate :: KnownNat p => Int -> F p -> Int -> Circuit (F p)
constGate _ x n = [(v, q)] where
  v = [0, 0, n]
  q = [0, 0, -1, 0, x]
  -- the output wire ‘n’ contains the value ‘x’
  -- the input wires are not used
