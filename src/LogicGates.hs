{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-@ LIQUID "--reflection" @-}
{-@ embed GHC.Num.Natural.Natural as int @-}
module LogicGates (andGate) where

import Constraints
import PrimitiveRoot
-- import Data.Vector (fromList)
import Vec

{-@ notGate :: Circuit (F p) 2 3 @-} -- 2 gates, 3 wires
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


{-@ orGate :: Circuit (F p) 5 5 @-} -- 3 gates, 5 wires
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
