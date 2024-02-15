module Constraints where

import Data.FiniteField.PrimeField
import GHC.TypeNats (KnownNat)

import Data.Vector (Vector, (!))

-- n == # gates
-- m == # wires

-- TODO: should use vectors/polynomials instead of lists?

type F p = PrimeField p        -- prime field
type Selector p = Vector (F p) -- exactly n field elements

-- Gate wirings (each vector contains exactly ‘n’ integers in {1..m}):
type V = (Vector Int, Vector Int, Vector Int)
-- This should be thought of as 3 mappings from one of the ‘n’ gates to one of
-- the ‘m’ wires (‘left input’ wire, ‘right input’ wire and ‘output’ wire)

-- Selector vectors:
type Q p = (Selector p, -- (L)eft input
            Selector p, -- (R)ight input
            Selector p, -- (O)utput
            Selector p, -- (M)ultiplication
            Selector p) -- (C)onstant

type Circuit p = (V, Q p)

{-@ satisfies :: input:Vector (F p) ->
                 ((a,b,c), (qL,qR,qO,qM,qC)):Circuit p ->
                 Bool
@-}
-- Check that the input (values in wires) satisfies the circuit:
satisfies :: KnownNat p => Vector (F p) -> Circuit p -> Bool
satisfies input circuit@((a,b,c), (qL,qR,qO,qM,qC)) =
  and $ [checkGate input (i-1) | i <- [1..length a]] where
  checkGate x i = let xai = x!(a!i); xbi = x!(b!i); xci = x!(c!i) in
    (qL!i)*xai + (qR!i)*xbi + (qO!i)*xci + (qM!i)*xai*xbi + (qC!i) == 0
