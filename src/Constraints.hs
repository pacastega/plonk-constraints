{-# LANGUAGE FlexibleContexts #-}
module Constraints (polyEncoding, zH) where

import Interpolation (interpolateRoots)
import PrimitiveRoot

import Data.FiniteField.PrimeField
import GHC.TypeNats (KnownNat)
import Data.Poly
import Data.Vector (Vector, (!), generate)

import RefinementTypes()

-- n == # gates
-- m == # wires

type F p = PrimeField p        -- prime field
{-@ type Selector pf N = VectorN pf N @-}
type Selector pf = Vector pf -- exactly n field elements

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
                 Circuit (F p) n m ->
                 Bool @-}
-- Check that the input (values in wires) satisfies the circuit:
satisfies :: KnownNat p => Int -> Int -> Vector (F p) -> Circuit (F p) -> Bool
satisfies n _m input ((a,b,c), (qL,qR,qO,qM,qC)) =
  and $ [checkGate input i | i <- [0..n-1]] where
  {-@ checkGate :: x:VectorN (F p) _m -> Btwn Int 0 n -> Bool @-}
  checkGate x i = let xai = x!(a!i); xbi = x!(b!i); xci = x!(c!i) in
    (qL!i)*xai + (qR!i)*xbi + (qO!i)*xci + (qM!i)*xai*xbi + (qC!i) == 0

{-@ assume enumFromTo :: a:t -> b:t -> [{c:t | a <= c && c <= b}] @-}
{-@ assume generate :: n:Nat -> ({v:Nat | v < n} -> t) -> VectorN t n @-}

-- The goal is to prove that this polynomial vanishes at 0...n-1. To do this, we
-- show that (zH n) divides it evenly.
{-@ polyEncoding :: p:{v:Nat|v>=2} -> n:{v:Nat|v>0} -> m:Nat ->
                    VectorN (F p) m ->
                    Circuit (F p) n m ->
                    VPoly (F p) @-}
polyEncoding :: (KnownNat p, PrimitiveRoot (F p)) =>
                Int -> Int -> Int -> Vector (F p) -> Circuit (F p) -> VPoly (F p)
polyEncoding p n _m input ((a,b,c), (qL,qR,qO,qM,qC)) =
  qL'*a' + qR'*b' + qO'*c' + qM'*a'*b' + qC'
    where

      getInput gatePort i = input!(gatePort!i)
      {-@ getInput :: VectorN (Wire _m) n -> Btwn Int 0 n -> F p @-}

      a' = interpolateRoots p n (generate n (getInput a))
      b' = interpolateRoots p n (generate n (getInput b))
      c' = interpolateRoots p n (generate n (getInput c))

      qL' = interpolateRoots p n qL
      qR' = interpolateRoots p n qR
      qO' = interpolateRoots p n qO
      qM' = interpolateRoots p n qM
      qC' = interpolateRoots p n qC

-- zH n is the polynomial that vanishes precisely on the n-th roots of unity
zH :: KnownNat p => Word -> VPoly (F p)
zH n = (monomial n 1) - (monomial 0 1) -- X^n - 1
