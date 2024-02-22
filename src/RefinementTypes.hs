{-# OPTIONS -Wno-unused-imports -Wno-missing-export-lists #-}
module RefinementTypes where

import Data.Vector

{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}
{-@ type Btwn t A B = {v:t | A <= v && v < B} @-} -- [A..B)
