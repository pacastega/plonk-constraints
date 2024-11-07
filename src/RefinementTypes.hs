{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}

{-# OPTIONS -Wno-unused-imports -Wno-missing-export-lists #-}
module RefinementTypes where


{-@ type Nat1 = {v:Nat | v >= 1} @-}

{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type Btwn A B = {v:Int | A <= v && v < B} @-} -- [A..B)
