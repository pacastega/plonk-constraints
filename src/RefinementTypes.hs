{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}

{-# OPTIONS -Wno-unused-imports -Wno-missing-export-lists #-}
module RefinementTypes where


import Data.Vector
import Vec

{-@ type Nat1 = {v:Nat | v >= 1} @-}

{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}
{-@ type VecN a N = {v:Vec a | vvlen v == N} @-}
{-@ type Btwn A B = {v:Int | A <= v && v < B} @-} -- [A..B)
