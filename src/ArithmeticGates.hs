{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed GHC.Num.Natural.Natural as int @-}
module ArithmeticGates (addGate, mulGate, isZeroGate) where

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


{-@ reflect isZeroGate @-}
{-@ isZeroGate :: m:{v:Int | v >= 3} ->
                  ListN (Btwn 0 m) 3 ->
                  Circuit p 2 m @-} -- 2 gate, m wires
isZeroGate :: Num p => Int -> [Int] -> Circuit p
isZeroGate _ [a, w, c] =
  [([a, w, c], [ 0,  0, -1, -1,  1]), -- 1.
   ([a, c, 0], [ 0,  0,  0, -1,  0])] -- 2.

  -- Gate 1. 1 - a*w == c <=> 0 + 0 - c - a*w + 1 == 0
  -- Gate 2. a*c == 0 (a is 0, or c is false)
