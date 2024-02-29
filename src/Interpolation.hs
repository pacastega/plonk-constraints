{-# LANGUAGE FlexibleContexts #-}
module Interpolation (interpolate, interpolateRoots) where

import Data.Poly
import qualified Data.Vector as V
import qualified Data.FiniteField.PrimeField as PF
import GHC.TypeNats (KnownNat)

import PrimitiveRoot

import RefinementTypes()

type F p = PF.PrimeField p

-- Naïve Lagrange interpolation algorithm
{-@ interpolate :: n:Nat ->
                   VectorN (F p) n -> VectorN (F p) n -> VPoly (F p) @-}
interpolate :: KnownNat p => Int ->
               V.Vector (F p) -> V.Vector (F p) -> VPoly (F p)
interpolate _ xs ys = V.sum $ V.zipWith interpolateAt xs ys where
  term = monomial 0 -- independent term (monomial of degree 0)
  interpolateAt x y = term y * V.product (V.map (quotient x) (otherXs x))
  quotient x x' = (X - term x') * term (recip (x - x')) -- (X-x’)/(x-x’)
  otherXs x = V.filter (/= x) xs


-- Interpolate at the order-n subgroup {x ∈ F_p : x^n == 1}
{-@ interpolateRoots :: p:{v:Nat | v >= 2} ->
                        n:{v:Nat | v > 0 && (p-1) mod v == 0} ->
                        ys:VectorN (F p) n -> VPoly (F p) @-}
interpolateRoots :: (KnownNat p, PrimitiveRoot (F p)) =>
                    Int -> Int -> V.Vector (F p) -> VPoly (F p)
interpolateRoots p n ys = V.sum $ V.zipWith interpolateAt nthRoots ys where
  nthRoots = V.iterateN n (* primitiveNthRoot) 1
  primitiveNthRoot = primitiveRoot ^ ((p-1) `div` n)
  term = monomial 0 -- monomial of degree 0

  -- interpolateAt :: F p -> F p -> VPoly (F p)
  interpolateAt x y = term y * basisPoly where
    basisPoly = term (x * recip (fromIntegral n)) * quotient
    (quotient, _) = quotRemFractional numerator denominator
    numerator = monomial (fromIntegral n) 1 - term 1
    denominator = X - term x
