{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Constraints (checkGate, satisfies, F, Circuit) where

import Data.FiniteField.PrimeField
import GHC.TypeNats (KnownNat)

import Vec
import RefinementTypes()


type F = PrimeField

-- n == # gates
-- m == # wires

{-@ type Gate p M = (ListN (Btwn Int 0 M) 3, ListN p 5) @-}
type Gate p = ([Int], [p])

{-@ type Circuit p N M = {v:[Gate p M] | len v = N} @-}
type Circuit p = [Gate p]


{-@ reflect checkGate @-}
{-@ checkGate :: m:Nat -> VecN (F p) m -> Gate (F p) m -> Bool @-}
checkGate :: KnownNat p => Int -> Vec (F p) -> Gate (F p) -> Bool
checkGate _ x ([a,b,c], [qL,qR,qO,qM,qC]) =
  qL*x!a + qR*x!b + qO*x!c + qM*x!a*x!b + qC == 0


{-@ reflect satisfies @-}
{-@ satisfies :: n:Nat -> m:Nat -> VecN (F p) m -> Circuit (F p) n m -> Bool @-}
-- Check that the input (values in wires) satisfies the circuit:
satisfies :: KnownNat p => Int -> Int -> Vec (F p) -> Circuit (F p) -> Bool
satisfies _ _ _     []     = True
satisfies n m input (g:gs) = checkGate m input g && satisfies (n-1) m input gs


-- TODO: ‘transpose’ function to convert back to plonkish circuits
