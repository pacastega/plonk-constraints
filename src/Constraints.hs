{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Constraints (checkGate, satisfies, F, Circuit, V, Q) where

import Data.FiniteField.PrimeField
import GHC.TypeNats (KnownNat)

import Vec (Vec, index)
import Utils
import RefinementTypes()

-- n == # gates
-- m == # wires

type F p = PrimeField p        -- prime field
{-@ type Selector pf N = VecN pf N @-}
type Selector pf = Vec pf -- exactly n field elements

{-@ type Wire M = Btwn Int 0 M @-}
-- Gate wirings (each vector contains exactly ‘n’ integers in {0..m-1}):
{-@ type V N M =
     (VecN (Wire M) N, VecN (Wire M) N, VecN (Wire M) N) @-}
type V = (Vec Int, Vec Int, Vec Int)
-- This should be thought of as 3 mappings from one of the ‘n’ gates to one of
-- the ‘m’ wires (‘left input’ wire, ‘right input’ wire and ‘output’ wire)

-- Selector vectors:
{-@ type Q p N =
     (Selector p N, Selector p N, Selector p N, Selector p N, Selector p N) @-}
type Q p = (Selector p, -- (L)eft input
            Selector p, -- (R)ight input
            Selector p, -- (O)utput
            Selector p, -- (M)ultiplication
            Selector p) -- (C)onstant

{-@ type Circuit p N M = (V N M, Q p N) @-}
type Circuit p = (V, Q p)


{-@ reflect checkGate @-}
{-@ checkGate :: n:Nat -> m:Nat ->
                 VecN (F p) m -> Circuit (F p) n m -> Btwn Int 0 n ->
                 Bool @-}
checkGate :: KnownNat p =>
             Int -> Int -> Vec (F p) -> Circuit (F p) -> Int -> Bool
checkGate _ _ x ((a,b,c), (qL,qR,qO,qM,qC)) i =
  let (!) = index;
      xai = x!(a!i); xbi = x!(b!i); xci = x!(c!i) in
    (qL!i)*xai + (qR!i)*xbi + (qO!i)*xci + (qM!i)*xai*xbi + (qC!i) == 0


{-@ reflect satisfies @-}
{-@ satisfies :: n:Nat1 -> m:Nat ->
                 VecN (F p) m ->
                 Circuit (F p) n m ->
                 Bool @-}
-- Check that the input (values in wires) satisfies the circuit:
satisfies :: KnownNat p => Int -> Int -> Vec (F p) -> Circuit (F p) -> Bool
satisfies n m input circuit = allRange 0 n (checkGate n m input circuit)
