{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed GHC.Num.Natural.Natural as int @-}
module LogicGates where

import Utils (allRange) -- needed to use ‘satisfies’ in the reflection
import Constraints
import GHC.TypeNats (KnownNat)
import PrimitiveRoot
import Vec

{-@ reflect notGate @-}
{-@ notGate :: Circuit (F p) 2 2 @-} -- 2 gates, 2 wires
notGate :: PrimitiveRoot (F p) => Circuit (F p)
notGate = (v, q) where
  f = fromList
  v = (f [ 0,  0], -- left inputs
       f [ 0,  0], -- right inputs
       f [ 1,  0]) -- outputs

  q = (f [-1, -1], -- qL
       f [ 0,  0], -- qR
       f [-1,  0], -- qO
       f [ 0,  1], -- qM
       f [ 1,  0]) -- qC
  --       1.  2.

  -- Gate 1. 1 - w0 == w1
  -- Gate 2. w0 * w0 == w0 (w0 is boolean)

{-@ verifyNot :: VecN (F p) 3 -> {v:Bool | v} @-}
verifyNot :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
verifyNot x = notIsCorrect == satisfies 2 3 x gate where
  (!) = index
  gate@((a,b,c), _) = notGate
  notIsCorrect = (1 - x!(a!0) == x!(c!0)) &&    -- ‘not’ holds
                 (x!(a!1) * x!(b!1) == x!(a!1)) -- boolean


{-@ reflect andGate @-}
{-@ andGate :: Circuit (F p) 3 3 @-} -- 3 gates, 3 wires
andGate :: PrimitiveRoot (F p) => Circuit (F p)
andGate = (v, q) where
  f = fromList
  v = (f [0,   0,  1], -- left inputs
       f [1,   0,  1], -- right inputs
       f [2,   0,  0]) -- outputs

  q = (f [ 0, -1, -1], -- qL
       f [ 0,  0,  0], -- qR
       f [-1,  0,  0], -- qO
       f [ 1,  1,  1], -- qM
       f [ 0,  0,  0]) -- qC
  --      1.   2.  3.

  -- Gate 1. w0 * w1 == w2
  -- Gate 2. w0 * w0 == w0 (w0 is boolean)
  -- Gate 3. w1 * w1 == w1 (w1 is boolean)

{-@ verifyAnd :: VecN (F p) 3 -> {v:Bool | v} @-}
verifyAnd :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
verifyAnd x = andIsCorrect == satisfies 3 3 x gate where
  (!) = index
  gate@((a,b,c), _) = andGate
  andIsCorrect = (x!(c!0) == if x!(a!0) == 0 || x!(b!0) == 0
                   then 0 else 1) &&               -- and holds
                 (x!(a!1) * x!(b!1) == x!(a!1)) && -- boolean
                 (x!(a!2) * x!(b!2) == x!(a!2))    -- boolean


{-@ reflect orGate @-}
{-@ orGate :: Circuit (F p) 5 5 @-} -- 5 gates, 5 wires
orGate :: PrimitiveRoot (F p) => Circuit (F p)
orGate = (v, q) where
  f = fromList
  v = (f [ 0,  0,  3,  0,  1], -- left inputs
       f [ 1,  1,  4,  0,  1], -- right inputs
       f [ 3,  4,  2,  0,  0]) -- outputs

  q = (f [ 1,  0,  1, -1, -1], -- qL
       f [ 1,  0, -1,  0,  0], -- qR
       f [-1, -1, -1,  0,  0], -- qO
       f [ 0,  1,  0,  1,  1], -- qM
       f [ 0,  0,  0,  0,  0]) -- qC
  --       1.  2.  3.  4.  5.

  -- Gate 1. w0 + w1 == w3
  -- Gate 2. w0 * w1 == w4
  -- Gate 3. w3 - w4 == w2
  -- Gate 4. w0 * w0 == w0 (w0 is boolean)
  -- Gate 5. w1 * w1 == w1 (w1 is boolean)

{-@ verifyOr :: VecN (F p) 5 -> {v:Bool | v} @-}
verifyOr :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
verifyOr x = orIsCorrect == satisfies 5 5 x gate where
  (!) = index
  gate@((a,b,c), _) = orGate
  orIsCorrect = (x!(c!2) == if x!(a!0) == 1 || x!(b!0) == 1
                  then 1 else 0) &&               -- or holds

                -- internal properties:
                checkGate 5 5 x gate 1 &&         -- internal gate 1 works
                checkGate 5 5 x gate 2 &&         -- internal gate 2 works

                (x!(a!3) * x!(b!3) == x!(a!3)) && -- boolean
                (x!(a!4) * x!(b!4) == x!(a!4))    -- boolean


{-@ reflect xorGate @-}
{-@ xorGate :: Circuit (F p) 5 5 @-} -- 5 gates, 5 wires
xorGate :: PrimitiveRoot (F p) => Circuit (F p)
xorGate = (v, q) where
  f = fromList
  v = (f [ 0,  0,  3,  0,  1], -- left inputs
       f [ 1,  1,  4,  0,  1], -- right inputs
       f [ 3,  4,  2,  0,  0]) -- outputs

  q = (f [ 1,  0,  1, -1, -1], -- qL
       f [ 1,  0, -2,  0,  0], -- qR
       f [-1, -1, -1,  0,  0], -- qO
       f [ 0,  1,  0,  1,  1], -- qM
       f [ 0,  0,  0,  0,  0]) -- qC
  --       1.  2.  3.  4.  5.

  -- Gate 1. w0 +   w1 == w3
  -- Gate 2. w0 *   w1 == w4
  -- Gate 3. w3 - 2*w4 == w2
  -- Gate 4. w0 *   w0 == w0 (w0 is boolean)
  -- Gate 5. w1 *   w1 == w1 (w1 is boolean)

{-@ verifyXor :: VecN (F p) 5 -> {v:Bool | v}@-}
verifyXor :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
verifyXor x = xorIsCorrect == satisfies 5 5 x gate where
  (!) = index
  gate@((a,b,c), _) = xorGate
  xorIsCorrect = (x!(c!2) == if x!(a!0) /= x!(b!0)
                   then 1 else 0) &&               -- xor holds

                 -- internal properties:
                 checkGate 5 5 x gate 1 &&         -- internal gate 1 works
                 checkGate 5 5 x gate 2 &&         -- internal gate 2 works

                 (x!(a!3) * x!(b!3) == x!(a!3)) && -- boolean
                 (x!(a!4) * x!(b!4) == x!(a!4))    -- boolean
