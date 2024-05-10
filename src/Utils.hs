{-@ LIQUID "--reflection" @-}
module Utils where

import RefinementTypes()

{-@ reflect fst' @-}
fst' :: (a, b) -> a
fst' (x, _) = x

{-@ reflect snd' @-}
snd' :: (a, b) -> b
snd' (_, y) = y

{-@ reflect append' @-}
{-@ append' :: xs:[a] -> ys:[a] ->
               {v:[a] | len v = len xs + len ys} @-}
append' :: [a] -> [a] -> [a]
append' [] ys     = ys
append' (x:xs) ys = x : append' xs ys

{-@ inline boolean @-}
boolean :: (Num p, Eq p) => p -> Bool
boolean x = x == 0 || x == 1
