module Constraints where

import Data.FiniteField.PrimeField
import GHC.TypeNats (KnownNat)

import Data.Vector (Vector, (!))
{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}
{-@ type Btwn t A B = {v:t | A <= v && v < B} @-} -- [A..B)

-- n == # gates
-- m == # wires

-- TODO: should use vectors/polynomials instead of lists?

type F p = PrimeField p        -- prime field
{-@ type Selector p N = VectorN (F p) N @-}
type Selector p = Vector (F p) -- exactly n field elements

{-@ type Wire M = Btwn Int 0 M @-}
-- Gate wirings (each vector contains exactly ‘n’ integers in {0..m-1}):
{-@ type V N M =
     (VectorN (Wire M) N, VectorN (Wire M) N, VectorN (Wire M) N) @-}
type V = (Vector Int, Vector Int, Vector Int)
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

{-@ satisfies :: n:Nat -> m:Nat ->
                 VectorN (F p) m ->
                 Circuit p n m ->
                 Bool @-}
-- Check that the input (values in wires) satisfies the circuit:
satisfies :: KnownNat p => Int -> Int -> Vector (F p) -> Circuit p -> Bool
satisfies n m input ((a,b,c), (qL,qR,qO,qM,qC)) =
  and $ [checkGate input i | i <- [0..n-1]] where
  {-@ checkGate :: x:VectorN (F p) m -> Btwn Int 0 n -> Bool @-}
  checkGate x i = let xai = x!(a!i); xbi = x!(b!i); xci = x!(c!i) in
    (qL!i)*xai + (qR!i)*xbi + (qO!i)*xci + (qM!i)*xai*xbi + (qC!i) == 0

{-@ assume enumFromTo :: a:t -> b:t -> [{c:t | a <= c && c <= b}] @-}
