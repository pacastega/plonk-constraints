{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module ArithmeticGates where

import Constraints
import Vec

import TypeAliases

{-@ reflect addGate @-}
{-@ addGate :: m:Nat ->
               ListN (Btwn 0 m) 3 ->
               Circuit p 1 m @-} -- 1 gate, m wires
addGate :: Num p => Int -> [Int] -> Circuit p
addGate _ indices = [(v, q)] where
  v = indices
  q = [1, 1, -1, 0, 0]
  -- a+b == c <=> a + b - c + 0*m + 0 == 0

{-@ reflect addGateConst @-}
{-@ addGateConst :: m:Nat ->
                    k:p ->
                    ListN (Btwn 0 m) 2 ->
                    Circuit p 1 m @-} -- 1 gate, m wires
addGateConst :: Num p => Int -> p -> [Int] -> Circuit p
addGateConst _ k [a, c] = [(v, q)] where
  v = [a, 0, c]
  q = [1, 0, -1, 0, k]
  -- a+k == c <=> a + 0 - c + 0*m + k == 0


{-@ reflect linCombGate @-}
{-@ linCombGate :: m:Nat ->
                   ListN p 2 ->
                   ListN (Btwn 0 m) 3 ->
                   Circuit p 1 m @-} -- 1 gate, m wires
linCombGate :: Num p => Int -> [p] -> [Int] -> Circuit p
linCombGate m [k1, k2] indices = affCombGate m [k1, k2, 0] indices
-- k1*a + k2*b == c

{-@ reflect affCombGate @-}
{-@ affCombGate :: m:Nat ->
                   ListN p 3 ->
                   ListN (Btwn 0 m) 3 ->
                   Circuit p 1 m @-} -- 1 gate, m wires
affCombGate :: Num p => Int -> [p] -> [Int] -> Circuit p
affCombGate _ [k1, k2, k] indices = [(v, q)] where
  v = indices
  q = [k1, k2, -1, 0, k]
  -- k1*a + k2*b + k == c <=> k1*a + k2*b - c + 0*m + k == 0

{-@ reflect mulGate @-}
{-@ mulGate :: m:Nat ->
               ListN (Btwn 0 m) 3 ->
               Circuit p 1 m @-} -- 1 gate, m wires
mulGate :: Num p => Int -> [Int] -> Circuit p
mulGate _ indices = [(v, q)] where
  v = indices
  q = [0, 0, -1, 1, 0]
  -- a*b == c <=> 0 + 0 - c + a*b + 0 == 0

{-@ reflect mulGateConst @-}
{-@ mulGateConst :: m:Nat ->
                    k:p ->
                    ListN (Btwn 0 m) 2 ->
                    Circuit p 1 m @-} -- 1 gate, m wires
mulGateConst :: Num p => Int -> p -> [Int] -> Circuit p
mulGateConst _ k [a, c] = [(v, q)] where
  v = [a, 0, c]
  q = [k, 0, -1, 0, 0]
  -- a*k == c <=> k*a + 0 - c + 0*m + 0 == 0

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

{-@ reflect nonZeroGate @-}
{-@ nonZeroGate :: m:Int ->
                   ListN (Btwn 0 m) 2 ->
                   Circuit p 1 m @-} -- 1 gate, m wires
nonZeroGate :: Num p => Int -> [Int] -> Circuit p
nonZeroGate _ [a, w] = [([a, w, 0], [0, 0, 0, 1, -1])]
  -- a /= 0 <=> ∃w. a*w == 1 <=> 0 + 0 + 0 + a*w - 1 == 0

{-@ reflect boolGate @-}
{-@ boolGate :: m:Int ->
                Btwn 0 m ->
                Circuit p 1 m @-} -- 1 gate, m wires
boolGate :: Num p => Int -> Int -> Circuit p
boolGate _ a = [([a, a, 0], [-1, 0, 0, 1, 0])]
  -- a ∈ {0,1} <=> a*(a-1) == 0 <=> -a + 0 + 0 + a*a + 0 == 0

{-@ reflect equalGate @-}
{-@ equalGate :: m:Int ->
                 ListN (Btwn 0 m) 2 ->
                 Circuit p 1 m @-} -- 1 gate, m wires
equalGate :: Num p => Int -> [Int] -> Circuit p
equalGate _ [a, b] = [([a, b, 0], [1, -1, 0, 0, 0])]
  -- a == b <=> a-b == 0
