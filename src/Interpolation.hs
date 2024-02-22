module Interpolation (interpolate) where

import Data.Poly
import qualified Data.Vector as V
import Data.FiniteField.PrimeField
import GHC.TypeNats (KnownNat)

import RefinementTypes()

type F p = PrimeField p

-- maybe generalise to a ring
-- maybe use a better algorithm (e.g. divide and conquer for the basis

-- Naïve Lagrange interpolation algorithm
{-@ interpolate :: KnownNat p -> n:Nat ->
                   VectorN (F p) n -> VectorN (F p) n -> VPoly (F p) @-}
interpolate :: KnownNat p => Int -> V.Vector (F p) -> V.Vector (F p) -> VPoly (F p)
interpolate _ xs ys = V.sum $ V.zipWith interpolateAt xs ys where
  term = monomial 0 -- independent term (monomial of degree 0)
  interpolateAt x y = term y * V.product (V.map (quotient x) (otherXs x))
  quotient x x' = (X - term x') * term (recip (x - x')) -- (X-x’)/(x-x’)
  otherXs x = V.filter (/= x) xs
