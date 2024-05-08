{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed GHC.Num.Natural.Natural as int @-}
module ArithmeticGates (addGate, mulGate, isZeroWitness) where

import Constraints
import Vec

{-@ reflect addGate @-}
{-@ addGate :: m:{v:Int | v >= 3} ->
               ListN (Btwn 0 m) 3 ->
               Circuit p 1 m @-} -- 1 gate, m wires
addGate :: Num p => Int -> [Int] -> Circuit p
addGate _ indices = [(v, q)] where
  v = indices
  q = [1, 1, -1, 0, 0]
  -- a+b == c <=> a + b - c + 0*m + 0 == 0

{-@ verifyAdd :: VecN p 3 -> {v:Bool | v} @-}
verifyAdd :: (Eq p, Num p) => Vec p -> Bool
verifyAdd x = sumIsCorrect == satisfies 1 3 x gate where
  gate@[([a,b,c], _)] = addGate 3 [0,1,2]
  sumIsCorrect = x!a + x!b == x!c


{-@ reflect mulGate @-}
{-@ mulGate :: m:{v:Int | v >= 3} ->
               ListN (Btwn 0 m) 3 ->
               Circuit p 1 m @-} -- 1 gate, m wires
mulGate :: Num p => Int -> [Int] -> Circuit p
mulGate _ indices = [(v, q)] where
  v = indices
  q = [0, 0, -1, 1, 0]
  -- a*b == c <=> 0 + 0 - c + a*b + 0 == 0

{-@ verifyMul :: VecN p 3 -> {v:Bool | v} @-}
verifyMul :: (Eq p, Num p) => Vec p -> Bool
verifyMul x = mulIsCorrect == satisfies 1 3 x gate where
  gate@[([a,b,c], _)] = mulGate 3 [0,1,2]
  mulIsCorrect = x!a * x!b == x!c


{-@ reflect isZeroWitness @-}
{-@ isZeroWitness :: m:{v:Int | v >= 3} ->
                     ListN (Btwn 0 m) 4 ->
                     Circuit p 3 m @-} -- 3 gate, m wires
isZeroWitness :: Num p => Int -> [Int] -> Circuit p
isZeroWitness _ [a, w, z, c] =
  [([a, w, c], [ 0,  0, -1, -1,  1]), -- 1.
   ([c, c, 0], [-1,  0,  0,  1,  0]), -- 2.
   ([w, z, 0], [ 0,  0,  0, -1,  1])] -- 3.

  -- Gate 1. 1 - a*w == c <=> 0 + 0 - c - a*w + 1 == 0
  -- Gate 2. c*c == c (c is boolean)
  -- Gate 3. w*z == 1 (w is always non-zero)
