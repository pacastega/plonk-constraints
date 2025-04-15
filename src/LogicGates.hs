{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module LogicGates where

import Constraints
import Vec

import TypeAliases

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
