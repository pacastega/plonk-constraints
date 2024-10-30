{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
module Vec where

{-@ type VecN a N = {v:Vec a | vvlen v == N} @-}
{-@ data Vec a = Nil | Cons {vx :: a, vxs :: Vec a} @-}
data Vec a = Nil | Cons a (Vec a)

instance Show a => Show (Vec a) where
  show v = "⟨" ++ show_ v ++ "⟩" where
    show_ (Nil)        = " "
    show_ (Cons x Nil) = show x
    show_ (Cons x xs)  = show x ++ "," ++ show_ xs

infixr 5 `Cons`

{-@ measure vvlen @-}
{-@ vvlen :: Vec a -> Nat @-}
vvlen :: Vec a -> Int
vvlen Nil         = 0
vvlen (Cons _ xs) = 1 + vvlen xs

{-@ infixl 9 ! @-}
{-@ reflect ! @-}
{-@ (!) :: xs:Vec a -> {n:Nat | n < vvlen xs} -> a @-}
(!) :: Vec a -> Int -> a
(!) (Cons x _)  0 = x
(!) (Cons _ xs) n = (!) xs (n-1)

infixl 9 !

{-@ reflect fromList @-}
{-@ fromList :: xs:[a] -> {v:Vec a | vvlen v == len xs} @-}
fromList :: [a] -> Vec a
fromList []     = Nil
fromList (x:xs) = x `Cons` fromList xs

{-@ reflect singleton @-}
{-@ singleton :: a -> {v:Vec a | vvlen v == 1} @-}
singleton :: a -> Vec a
singleton x = x `Cons` Nil

{-@ reflect append @-}
{-@ append :: xs:Vec a -> ys:Vec a ->
              {v:Vec a | vvlen v == vvlen xs + vvlen ys} @-}
append :: Vec a -> Vec a -> Vec a
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

{-@ reflect velem @-}
velem :: Eq a => a -> Vec a -> Bool
velem _ Nil         = False
velem x (Cons y ys) = x == y || velem x ys
