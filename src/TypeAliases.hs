{-@ LIQUID "--reflection" @-}

module TypeAliases where
import GHC.Num.Integer (Integer (IS))

{-@ type Nat1 = {v:Int | v >= 1} @-}

{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type Btwn A B = {v:Int | A <= v && v < B} @-} -- [A..B)

-- tries to fix 9971f17cde80c9cfe0b895f8f0204db96f16dafb
{-@ define fromInteger x = (x) @-}
-- {-@ define fromIntegral x = (x) @-}
{-@ define IS x = (x) @-}
-- {-@ define div x y = (x / y) @-}
-- {-@ define (/) x y = (x / y) @-}
-- {-@ define mod x y = (x mod y) @-}
