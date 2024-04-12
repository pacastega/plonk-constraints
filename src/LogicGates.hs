{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}
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
notGate = [([0, 0, 1], [-1,  0, -1,  0,  1]), -- 1.
           ([0, 0, 0], [-1,  0,  0,  1,  0])] -- 2.
          --   a  b  c      qL  qR  qO  qM  qC

  -- Gate 1. 1 - w0 == w1 (w1 = ¬ w0)
  -- Gate 2. w0 * w0 == w0 (w0 is boolean)

-- {-@ verifyNot :: VecN (F p) 3 -> {v:Bool | v} @-}
-- verifyNot :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
-- verifyNot x = notIsCorrect == satisfies 2 3 x gate where
--   gate@([a,b,c], _) = notGate
--   notIsCorrect = (1 - x!(a!0) == x!(c!0)) &&    -- ‘not’ holds
--                  (x!(a!1) * x!(b!1) == x!(a!1)) -- boolean


{-@ reflect andGate @-}
{-@ andGate :: Circuit (F p) 3 3 @-} -- 3 gates, 3 wires
andGate :: PrimitiveRoot (F p) => Circuit (F p)
andGate = [([0, 1, 2], [ 0,  0, -1,  1,  0]), -- 1.
           ([0, 0, 0], [-1,  0,  0,  1,  0]), -- 2.
           ([1, 1, 0], [-1,  0,  0,  1,  0])] -- 3.
          --   a  b  c      qL  qR  qO  qM  qC

  -- Gate 1. w0 * w1 == w2 (w2 = w0 ∧ w1)
  -- Gate 2. w0 * w0 == w0 (w0 is boolean)
  -- Gate 3. w1 * w1 == w1 (w1 is boolean)

-- {-@ verifyAnd :: VecN (F p) 3 -> {v:Bool | v} @-}
-- verifyAnd :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
-- verifyAnd x = andIsCorrect == satisfies 3 3 x gate where
--   gate@([a,b,c], _) = andGate
--   andIsCorrect = (x!(c!0) == if x!(a!0) == 0 || x!(b!0) == 0
--                    then 0 else 1) &&               -- and holds
--                  (x!(a!1) * x!(b!1) == x!(a!1)) && -- boolean
--                  (x!(a!2) * x!(b!2) == x!(a!2))    -- boolean


{-@ reflect orGate @-}
{-@ orGate :: Circuit (F p) 3 3 @-} -- 3 gates, 3 wires
orGate :: PrimitiveRoot (F p) => Circuit (F p)
orGate = [([0, 1, 2], [ 1,  1, -1, -1,  0]), -- 1.
          ([0, 0, 0], [-1,  0,  0,  1,  0]), -- 2.
          ([1, 1, 0], [-1,  0,  0,  1,  0])] -- 3.
         --   a  b  c      qL  qR  qO  qM  qC

  -- Gate 1. w0 + w1 - w0*w1 == w2 (w2 = w0 ∨ w1)
  -- Gate 2. w0 * w0 == w0 (w0 is boolean)
  -- Gate 3. w1 * w1 == w1 (w1 is boolean)

-- {-@ verifyOr :: VecN (F p) 3 -> {v:Bool | v} @-}
-- verifyOr :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
-- verifyOr x = orIsCorrect == satisfies 3 3 x gate where
--   gate@([a,b,c], _) = orGate
--   orIsCorrect = (x!(c!0) == if x!(a!0) == 1 || x!(b!0) == 1
--                   then 1 else 0) &&               -- or holds
--                 (x!(a!1) * x!(b!1) == x!(a!1)) && -- boolean
--                 (x!(a!2) * x!(b!2) == x!(a!2))    -- boolean


{-@ reflect xorGate @-}
{-@ xorGate :: Circuit (F p) 3 3 @-} -- 3 gates, 3 wires
xorGate :: PrimitiveRoot (F p) => Circuit (F p)
xorGate = [([0, 1, 2], [ 1,  1, -1, -2,  0]), -- 1.
           ([0, 0, 0], [-1,  0,  0,  1,  0]), -- 2.
           ([1, 1, 0], [-1,  0,  0,  1,  0])] -- 3.
          --   a  b  c      qL  qR  qO  qM  qC

  -- Gate 1. w0 + w1 -2*w0*w1 == w2 (w2 = w0 ⊕ w1)
  -- Gate 2. w0 * w0 == w0 (w0 is boolean)
  -- Gate 3. w1 * w1 == w1 (w1 is boolean)

-- {-@ verifyXor :: VecN (F p) 3 -> {v:Bool | v}@-}
-- verifyXor :: (KnownNat p, PrimitiveRoot (F p)) => Vec (F p) -> Bool
-- verifyXor x = xorIsCorrect == satisfies 3 3 x gate where
--   gate@([a,b,c], _) = xorGate
--   xorIsCorrect = (x!(c!0) == if x!(a!0) /= x!(b!0)
--                    then 1 else 0) &&               -- xor holds
--                  (x!(a!1) * x!(b!1) == x!(a!1)) && -- boolean
--                  (x!(a!2) * x!(b!2) == x!(a!2))    -- boolean
