{-@ LIQUID "--reflection" @-}

module TypeAliases where
import GHC.Num.Integer (Integer (IS))

{-@ type Nat1 = {v:Int | v >= 1} @-}

{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type Btwn A B = {v:Int | A <= v && v < B} @-} -- [A..B)

{-@ type TRUE = {b:Bool | b} @-}

{-@ define fromInteger x = (x) @-}
{-@ define IS x = (x) @-}
