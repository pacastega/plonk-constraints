{-@ LIQUID "--reflection" @-}
module Vec where

{-@ data Vec  a  = Nil | Cons {vx :: a,  vxs :: Vec a} @-}
data Vec a = Nil | Cons a (Vec a)
  deriving Show

infixr 5 `Cons`

{-@ measure vvlen @-}
{-@ vvlen :: Vec a -> Nat @-}
vvlen :: Vec a -> Int
vvlen Nil         = 0
vvlen (Cons _ xs) = 1 + vvlen xs

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
