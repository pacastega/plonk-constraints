{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed GHC.Num.Natural.Natural as int @-}
module ArithmeticGates (addGate, mulGate) where

import Utils (allRange) -- needed to use ‘satisfies’ in the reflection
import Constraints
import GHC.TypeNats (KnownNat)
import PrimitiveRoot
import Vec

{-@ reflect addGate @-}
{-@ addGate :: m:{v:Int | v >= 3} ->
               {v:[(Btwn Int 0 m)] | len v == 3} ->
               Circuit (F p) 1 m @-} -- 1 gate, m wires
addGate :: PrimitiveRoot (F p) => Int -> [Int] -> Circuit (F p)
addGate _ indices = (v, q) where
  f = fromList
  [l,r,o] = indices
  v = [f [l], f [r], f [o]]
  q = [f [1], f [1], f [-1], f [0], f [0]]
  -- a+b == c <=> a + b - c + 0*m + 0 == 0

{-@ verifyAdd :: VecN (F p) 3 -> {v:Bool | v} @-}
verifyAdd :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
verifyAdd x = sumIsCorrect == satisfies 1 3 x gate where
  gate@([a,b,c], _) = addGate 3 [0,1,2]
  sumIsCorrect = x!(a!0) + x!(b!0) == x!(c!0)


{-@ reflect mulGate @-}
{-@ mulGate :: m:{v:Int | v >= 3} ->
               {v:[(Btwn Int 0 m)] | len v == 3} ->
               Circuit (F p) 1 m @-} -- 1 gate, m wires
mulGate :: PrimitiveRoot (F p) => Int -> [Int] -> Circuit (F p)
mulGate _ indices = (v, q) where
  f = fromList
  [l,r,o] = indices
  v = [f [l], f [r], f [o]]
  q = [f [0], f [0], f [-1], f [1], f [0]]
  -- a*b == c <=> 0 + 0 - c + a*b + 0 == 0

{-@ verifyMul :: VecN (F p) 3 -> {v:Bool | v} @-}
verifyMul :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
verifyMul x = mulIsCorrect == satisfies 1 3 x gate where
  gate@([a,b,c], _) = mulGate 3 [0,1,2]
  mulIsCorrect = x!(a!0) * x!(b!0) == x!(c!0)
