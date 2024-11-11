{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module ArithmeticGates (addGate, mulGate, divGate,
                        isZeroGate, isEqlCGate) where

import Constraints
import Vec

{-@ reflect addGate @-}
{-@ addGate :: m:Nat ->
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
{-@ mulGate :: m:Nat ->
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

{-@ reflect divGate @-}
{-@ divGate :: m:Nat ->
               ListN (Btwn 0 m) 4 ->
               Circuit p 2 m @-}
divGate :: Num p => Int -> [Int] -> Circuit p
divGate _ [a, b, c, w] =
  [([b, c, a], [ 0,  0, -1,  1,  0]), -- 1.
   ([b, w, 0], [ 0,  0,  0,  1, -1])] -- 2.

  -- Gate 1. a/b == c <=> 0 + 0 - a + b*c + 0 == 0
  -- Gate 2. b*w == 1 (b is non-zero)

{-@ reflect isZeroGate @-}
{-@ isZeroGate :: m:Nat ->
                  ListN (Btwn 0 m) 3 ->
                  Circuit p 2 m @-} -- 2 gate, m wires
isZeroGate :: Num p => Int -> [Int] -> Circuit p
isZeroGate _ [a, w, c] =
  [([a, w, c], [ 0,  0, -1, -1,  1]), -- 1.
   ([a, c, 0], [ 0,  0,  0, -1,  0])] -- 2.

  -- Gate 1. 1 - a*w == c <=> 0 + 0 - c - a*w + 1 == 0
  -- Gate 2. a*c == 0 (a is 0, or c is false)


{-@ reflect isEqlCGate @-}
{-@ isEqlCGate :: m:Nat -> k:p ->
                  ListN (Btwn 0 m) 3 ->
                  Circuit p 2 m @-} -- 2 gate, m wires
isEqlCGate :: Num p => Int -> p -> [Int] -> Circuit p
isEqlCGate _ k [a, w, c] =
  [([a, w, c], [ 0,  k, -1, -1,  1]), -- 1.
   ([a, c, 0], [ 0,  k,  0, -1,  0])] -- 2.

  -- Gate 1. 1 - (a-k)*w == c <=> 0 + k*w - c - a*w + 1 == 0
  -- Gate 2. (a-k)*c == 0 (a is k, or c is false)
