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

{-@ reflect fst' @-}
fst' :: (a, b) -> a
fst' (x, _) = x

{-@ reflect snd' @-}
snd' :: (a, b) -> b
snd' (_, y) = y

{-@ reflect zipWith' @-}
{-@ zipWith' :: (a -> b -> c) ->
                xs:[a] -> ys:{[b] | len ys = len xs} ->
                zs:{[c] | len zs = len xs} @-}
zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' _ []     []     = []
zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys


{-@ reflect append' @-}
{-@ append' :: xs:[a] -> ys:[a] ->
               {v:[a] | len v = len xs + len ys} @-}
append' :: [a] -> [a] -> [a]
append' [] ys     = ys
append' (x:xs) ys = x : append' xs ys
