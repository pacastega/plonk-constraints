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
emptyCircuit _ = ([Nil,Nil,Nil], [Nil,Nil,Nil,Nil,Nil])

{-@ reflect constGate @-}
{-@ constGate :: m:Nat -> F p -> Btwn Int 0 m -> Circuit (F p) 1 m @-}
constGate :: KnownNat p => Int -> F p -> Int -> Circuit (F p)
constGate _ x n = let f = singleton in
  ([f 0, f 0, f n], [f 0, f 0, f (-1), f 0, f x])
  -- the output wire ‘n’ contains the value ‘x’
  -- the input wires are not used


{-@ reflect join @-}
{-@ join :: n1:Nat -> n2:Nat -> n:{v:Nat | v == n1 + n2} -> m:Nat ->
            Circuit (F p) n1 m -> Circuit (F p) n2 m ->
            Circuit (F p) n m @-}
join :: Int -> Int -> Int -> Int ->
        Circuit (F p) -> Circuit (F p) -> Circuit (F p)
join _ _ _ _ (v1, q1) (v2, q2) = (zipWith' append v1 v2, zipWith' append q1 q2)
