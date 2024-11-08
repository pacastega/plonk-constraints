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


{-@ measure GHC.Num.fromInteger :: Int -> Int @-}
{-@ measure GHC.Num.Integer.IS :: a -> b @-}

{-@ reflect boolean @-}
boolean :: (Num p, Eq p) => p -> Bool
boolean x = x == 0 || x == 1

-- Exponentiate by repeated multiplication
{-@ reflect pow @-}
{-@ pow :: a -> n:Nat -> a / [n] @-}
pow :: Num a => a -> Int -> a
pow _ 0 = 1
pow x n = x * (pow x (n-1))

{-@ reflect mkList2 @-}
mkList2 :: a -> a -> [a]
mkList2 x y = [x, y]

{-@ reflect mkList3 @-}
mkList3 :: a -> a -> a -> [a]
mkList3 x y z = [x, y, z]
