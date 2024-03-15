{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed GHC.Num.Natural.Natural as int @-}
module Circuits where

import Constraints
import GHC.TypeNats (KnownNat)
import PrimitiveRoot
import Vec
import Utils (min')

{-@ emptyCircuit :: m:Nat -> Circuit (F p) 0 m @-}
emptyCircuit :: KnownNat p => Int -> Circuit (F p)
emptyCircuit _ = ([Nil,Nil,Nil], [Nil,Nil,Nil,Nil,Nil])

{-@ constGate :: m:Nat -> F p -> Btwn Int 0 m -> Circuit (F p) 1 m @-}
constGate :: KnownNat p => Int -> F p -> Int -> Circuit (F p)
constGate _ x n = let f = singleton in
  ([f 0, f 0, f n], [f 0, f 0, f (-1), f 0, f x])
  -- the output wire ‘n’ contains the value ‘x’
  -- the input wires are not used


{-@ join :: n1:Nat -> n2:Nat -> n:{v:Nat | v == n1 + n2} -> m:Nat ->
            Circuit (F p) n1 m -> Circuit (F p) n2 m ->
            Circuit (F p) n m @-}
join :: KnownNat p => Int -> Int -> Int -> Int ->
                      Circuit (F p) -> Circuit (F p) -> Circuit (F p)
join _ _ _ _ (v1, q1) (v2, q2) = (zipWith append v1 v2, zipWith append q1 q2)

{-@ assume zipWith :: (a -> b -> c) -> x:[a] -> y:[b] ->
                      {v:[c] | len v == min' (len x) (len y)} @-}
