{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Constraints (checkGate, satisfies, Circuit) where

import Vec
import RefinementTypes()


-- n == # gates
-- m == # wires

{-@ type Gate p M = (ListN (Btwn 0 M) 3, ListN p 5) @-}
type Gate p = ([Int], [p])

{-@ type Circuit p N M = ListN (Gate p M) N @-}
type Circuit p = [Gate p]


{-@ reflect checkGate @-}
{-@ checkGate :: m:Nat -> VecN p m -> Gate p m -> Bool @-}
checkGate :: (Eq p, Num p) => Int -> Vec p -> Gate p -> Bool
checkGate _ x ([a,b,c], [qL,qR,qO,qM,qC]) =
  qL*x!a + qR*x!b + qO*x!c + qM*x!a*x!b + qC == 0


{-@ reflect satisfies @-}
{-@ satisfies :: n:Nat -> m:Nat -> VecN p m -> Circuit p n m -> Bool @-}
-- Check that the input (values in wires) satisfies the circuit:
satisfies :: (Eq p, Num p) => Int -> Int -> Vec p -> Circuit p -> Bool
satisfies _ _ _     []     = True
satisfies n m input (g:gs) = checkGate m input g && satisfies (n-1) m input gs


-- TODO: ‘transpose’ function to convert back to plonkish circuits
