{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Utils where

import TypeAliases
import Language.Haskell.Liquid.ProofCombinators ((?))

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

{-@ reflect map' @-}
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

{-@ reflect liftA2' @-}
liftA2' :: (a -> b -> c) -> Maybe a -> Maybe b -> Maybe c
liftA2' f (Just x) (Just y) = Just (f x y)
liftA2' _ _ _ = Nothing

{-@ reflect fmap' @-}
fmap' :: (a -> b) -> Maybe a -> Maybe b
fmap' f (Just x) = Just (f x)
fmap' _ _ = Nothing

{-@ reflect max' @-}
-- {-@ max' :: a:Int -> b:Int -> {c:Int | c >= a && c >= b} @-}
max' :: Int -> Int -> Int
max' a b = if a > b then a else b


{-@ reflect enumFromTo' @-}
{-@ enumFromTo' :: a:Int -> b:Int
                -> {l:[{v:Int | a <= v && v <= b}] | len l = max' (b-a+1) 0}
                 / [b-a] @-}
enumFromTo' :: Int -> Int -> [Int]
enumFromTo' a b
  | a > b     = []
  | a == b    = [a]
  | otherwise = a : enumFromTo' (a+1) b

{-@ reflect firstNats @-}
{-@ firstNats :: n:Nat -> {l:[Btwn 0 n] | len l = n} @-}
firstNats :: Int -> [Int]
firstNats n = enumFromTo' 0 (n-1) ? max' n 0

{-@ measure length' @-}
length' :: [a] -> Int
length' []     = 0
length' (_:xs) = 1 + length' xs

{-@ reflect sum' @-}
sum' :: [Int] -> Int
sum' []     = 0
sum' (x:xs) = x + sum' xs

{-@ reflect zero @-}
{-@ zero :: {v:p | v ~~ 0} @-}
zero :: Num p => p
zero = fromInteger 0

{-@ reflect one @-}
{-@ one :: {v:p | v ~~ 1} @-}
one :: Num p => p
one = fromInteger 1
