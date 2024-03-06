{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed GHC.Num.Natural.Natural as int @-}
module ArithmeticGates (addGate, mulGate) where

import Constraints
import GHC.TypeNats (KnownNat)
import PrimitiveRoot
-- import Data.Vector (fromList, Vector, (!))
import Vec

{-@ reflect addGate @-}
{-@ addGate :: Circuit (F p) 1 3 @-} -- 1 gate, 3 wires
addGate :: PrimitiveRoot (F p) => Circuit (F p)
addGate = (v, q) where
  f = fromList
  v = (f [0], f [1], f [2])
  q = (f [1], f [1], f [-1], f [0], f [0])
  -- a+b == c <=> a + b - c + 0*m + 0 == 0

{-@ verifyAdd :: VecN (F p) 3 -> {v:Bool | v} @-}
verifyAdd :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
verifyAdd x = sumIsCorrect == checkGate 1 3 x gate 0 where
  (!) = index
  gate@((a,b,c), _) = addGate
  sumIsCorrect = x!(a!0) + x!(b!0) == x!(c!0)


{-@ mulGate :: Circuit (F p) 1 3 @-} -- 1 gate, 3 wires
mulGate :: PrimitiveRoot (F p) => Circuit (F p)
mulGate = (v, q) where
  f = fromList
  v = (f [0], f [1], f [2])
  q = (f [0], f [0], f [-1], f [1], f [0])
  -- a*b == c <=> 0 + 0 - c + a*b + 0 == 0

-- {-@ verifyMul :: VecN (F p) 3 -> {v:Bool | v} @-}
-- verifyMul :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
-- verifyMul input = let ((a,b,c), q) = mulGate;
--                       getInput port = input!(port!0) in
--   (getInput a * getInput b == getInput c) == (satisfies 1 3 input ((a,b,c), q))
