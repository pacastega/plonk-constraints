{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-@ embed GHC.Num.Natural.Natural as int @-}
module ArithmeticGates (addGate, mulGate) where

import Constraints
import GHC.TypeNats (KnownNat)
import PrimitiveRoot
import Data.Vector (fromList)
-- import RefinementTypes

type F17 = F 17
-- TODO: it seems to be necessary to include this type alias in *plain* Haskell
-- because Liquid Haskell complains that ‘the Liquid component {17} is
-- inconsistent with the Haskell component GHC.Types.Int’ if the liquid
-- annotation below has (F 17) instead of F17.
-- https://github.com/ucsd-progsys/liquidhaskell/issues/2080

{-@ addGate :: Circuit (F p) 1 3 @-}
addGate :: (KnownNat p, PrimitiveRoot (F p)) => Circuit (F p)
addGate = (v, q) where
  v = let f=fromList in (f [0], f [1], f [2])
  q = let f=fromList in (f [1], f [1], f [-1], f [0], f [0])
  -- a+b == c <=> a + b - c + 0*m + 0 == 0

{-@ mulGate :: Circuit (F p) 1 3 @-}
mulGate :: (KnownNat p, PrimitiveRoot (F p)) => Circuit (F p)
mulGate = (v, q) where
  v = let f=fromList in (f [0], f [1], f [2])
  q = let f=fromList in (f [0], f [0], f [-1], f [1], f [0])
  -- a*b == c <=> 0 + 0 - c + a*b + 0 == 0


-- TODO: how to properly verify these work for all possible inputs?
