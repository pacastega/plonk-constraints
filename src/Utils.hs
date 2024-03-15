{-@ LIQUID "--reflection" @-}
module Utils where

import RefinementTypes()

-- True <=> p holds for all integers in the range [a..b) (possibly empty)
{-@ reflect allRange @-}
{-@ allRange :: a:Int -> b:{v:Int | a <= v} ->
                (Btwn Int a b -> Bool) ->
                Bool
                / [b-a] @-}
allRange :: Int -> Int -> (Int -> Bool) -> Bool
allRange a b p
  | a == b    = True
  | otherwise = p a && allRange (a+1) b p

{-@ reflect min' @-}
min' :: Ord a => a -> a -> a
min' x y = if x < y then x else y
