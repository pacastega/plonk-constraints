{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module LogicGates where

import Constraints
import Vec

{-@ reflect notGate @-}
{-@ notGate :: m:Nat ->
               ListN (Btwn 0 m) 2 ->
               Circuit p 2 m @-} -- 2 gates, m wires
notGate :: Num p => Int -> [Int] -> Circuit p
notGate _ [a, c] =
  [([a, 0, c], [-1,  0, -1,  0,  1]), -- 1.
   ([a, a, 0], [-1,  0,  0,  1,  0])] -- 2.
  -- a  b  c    qL  qR  qO  qM  qC

  -- Gate 1. 1 - a == c (c = ¬ a)
  -- Gate 2. a * a == a (a is boolean)

{-@ verifyNot :: VecN p 3 -> {v:Bool | v} @-}
verifyNot :: (Eq p, Num p) => Vec p -> Bool
verifyNot x = notIsCorrect == satisfies 2 3 x gate where
  gate@[([a0,_,c0], _), ([a1,b1,_], _)] = notGate 2 [0,1]
  notIsCorrect = (1 - x!a0 == x!c0) &&    -- ‘not’ holds
                 (x!a1 * x!b1 == x!a1)    -- boolean


{-@ reflect andGate @-}
{-@ andGate :: m:Nat ->
               ListN (Btwn 0 m) 3 ->
               Circuit p 3 m @-} -- 3 gates, m wires
andGate :: Num p => Int -> [Int] -> Circuit p
andGate _ [a,b,c] =
  [([a, b, c], [ 0,  0, -1,  1,  0]), -- 1.
   ([a, a, 0], [-1,  0,  0,  1,  0]), -- 2.
   ([b, b, 0], [-1,  0,  0,  1,  0])] -- 3.
  -- a  b  c    qL  qR  qO  qM  qC

  -- Gate 1. a * b == c (c = a ∧ b)
  -- Gate 2. a * a == a (a is boolean)
  -- Gate 3. b * b == b (b is boolean)

{-@ verifyAnd :: VecN p 3 -> {v:Bool | v} @-}
verifyAnd :: (Eq p, Num p) => Vec p -> Bool
verifyAnd x = andIsCorrect == satisfies 3 3 x gate where
  gate@[([a0,b0,c0], _), ([a1,b1,_], _), ([a2,b2,_], _)] = andGate 3 [0,1,2]
  andIsCorrect = (x!c0 == if x!a0 == 0 || x!b0 == 0
                   then 0 else 1) &&               -- and holds
                 (x!a1 * x!b1 == x!a1) &&          -- boolean
                 (x!a2 * x!b2 == x!a2)             -- boolean


{-@ reflect orGate @-}
{-@ orGate :: m:Nat ->
              ListN (Btwn 0 m) 3 ->
              Circuit p 3 m @-} -- 3 gates, m wires
orGate :: Num p => Int -> [Int] -> Circuit p
orGate _ [a,b,c] =
  [([a, b, c], [ 1,  1, -1, -1,  0]), -- 1.
   ([a, a, 0], [-1,  0,  0,  1,  0]), -- 2.
   ([b, b, 0], [-1,  0,  0,  1,  0])] -- 3.
  -- a  b  c    qL  qR  qO  qM  qC

  -- Gate 1. a + b - a*b == c (c = a ∨ b)
  -- Gate 2. a * a == a (a is boolean)
  -- Gate 3. b * b == b (b is boolean)

{-@ verifyOr :: VecN p 3 -> {v:Bool | v} @-}
verifyOr :: (Eq p, Num p) => Vec p -> Bool
verifyOr x = orIsCorrect == satisfies 3 3 x gate where
  gate@[([a0,b0,c0], _), ([a1,b1,_], _), ([a2,b2,_], _)] = orGate 3 [0, 1, 2]
  orIsCorrect = (x!c0 == if x!a0 == 1 || x!b0 == 1
                  then 1 else 0) &&               -- or holds
                (x!a1 * x!b1 == x!a1) &&          -- boolean
                (x!a2 * x!b2 == x!a2)             -- boolean


{-@ reflect xorGate @-}
{-@ xorGate :: m:Nat ->
               ListN (Btwn 0 m) 3 ->
               Circuit p 3 m @-} -- 3 gates, m wires
xorGate :: Num p => Int -> [Int] -> Circuit p
xorGate _ [a,b,c] =
  [([a, b, c], [ 1,  1, -1, -2,  0]), -- 1.
   ([a, a, 0], [-1,  0,  0,  1,  0]), -- 2.
   ([b, b, 0], [-1,  0,  0,  1,  0])] -- 3.
  -- a  b  c    qL  qR  qO  qM  qC

  -- Gate 1. a + b -2*a*b == c (c = a ⊕ b)
  -- Gate 2. a * a == a (a is boolean)
  -- Gate 3. b * b == b (b is boolean)

{-@ verifyXor :: VecN p 3 -> {v:Bool | v} @-}
verifyXor :: (Eq p, Num p) => Vec p -> Bool
verifyXor x = xorIsCorrect == satisfies 3 3 x gate where
  gate@[([a0,b0,c0], _), ([a1,b1,_], _), ([a2,b2,_], _)] = xorGate 3 [0, 1, 2]
  xorIsCorrect = (x!c0 == if x!a0 /= x!b0
                   then 1 else 0) &&               -- xor holds
                 (x!a1 * x!b1 == x!a1) &&          -- boolean
                 (x!a2 * x!b2 == x!a2)             -- boolean

-- Unsafe boolean gates (assume the inputs are boolean) ------------------------
{-@ reflect unsafeNotGate @-}
{-@ unsafeNotGate :: m:Nat ->
                     ListN (Btwn 0 m) 2 ->
                     Circuit p 1 m @-} -- 1 gate, m wires
unsafeNotGate :: Num p => Int -> [Int] -> Circuit p
unsafeNotGate _ [a, c] = [([a, 0, c], [-1,  0, -1,  0,  1])]
                         -- a  b  c    qL  qR  qO  qM  qC

{-@ reflect unsafeAndGate @-}
{-@ unsafeAndGate :: m:Nat ->
                     ListN (Btwn 0 m) 3 ->
                     Circuit p 1 m @-} -- 1 gate, m wires
unsafeAndGate :: Num p => Int -> [Int] -> Circuit p
unsafeAndGate _ [a,b,c] = [([a, b, c], [ 0,  0, -1,  1,  0])]
                          -- a  b  c    qL  qR  qO  qM  qC

{-@ reflect unsafeOrGate @-}
{-@ unsafeOrGate :: m:Nat ->
                    ListN (Btwn 0 m) 3 ->
                    Circuit p 1 m @-} -- 1 gate, m wires
unsafeOrGate :: Num p => Int -> [Int] -> Circuit p
unsafeOrGate _ [a,b,c] = [([a, b, c], [ 1,  1, -1, -1,  0])]
                         -- a  b  c    qL  qR  qO  qM  qC

{-@ reflect unsafeXorGate @-}
{-@ unsafeXorGate :: m:Nat ->
                     ListN (Btwn 0 m) 3 ->
                     Circuit p 1 m @-} -- 1 gate, m wires
unsafeXorGate :: Num p => Int -> [Int] -> Circuit p
unsafeXorGate _ [a,b,c] = [([a, b, c], [ 1,  1, -1, -2,  0])]
                          -- a  b  c    qL  qR  qO  qM  qC
