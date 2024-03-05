{-@ LIQUID "--reflection" @-}

{-# OPTIONS -Wno-unused-imports -Wno-missing-export-lists #-}
module RefinementTypes where


import Data.Vector
import Vec

{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}
{-@ type VecN a N = {v:Vec a | vvlen v == N} @-}
{-@ type Btwn t A B = {v:t | A <= v && v < B} @-} -- [A..B)
