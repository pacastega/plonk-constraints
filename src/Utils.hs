{-@ LIQUID "--reflection" @-}
module Utils where

import TypeAliases

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

{-@ map' :: (a -> b) -> xs:[a] -> {ys:[b] | len ys = len xs} @-}
map' :: (a -> b) -> [a] -> [b]
map' _ []     = []
map' f (x:xs) = f x : map f xs

{-@ zipWith' :: (a -> b -> c)
             -> xs:[a]
             -> ys:{[b] | len ys = len xs}
             -> zs:{[c] | len zs = len xs} @-}
zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' _ [] []         = []
zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys

{-@ assume sequence' :: ms:[m a] -> m {l:[a] | len l = len ms} @-}
sequence' :: Monad m => [m a] -> m [a]
sequence' = sequence

{-@ reflect any' @-}
any' :: (a -> Bool) -> Maybe a -> Bool
any' _ Nothing  = False
any' p (Just x) = p x

{-@ liquidAssert :: {b:Bool | b} -> x:a -> {v:a | v == x && b} @-}
liquidAssert :: Bool -> a -> a
liquidAssert _ x = x

{-@ (??) :: x:b -> y:a -> {v:a | v == y} @-}
(??) :: b -> a -> a
_ ?? y = y

{-@ reflect foldr' @-}
foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' _ acc [] = acc
foldr' f acc (x:xs) = f x (foldr' f acc xs)
