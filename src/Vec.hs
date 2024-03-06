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

{-@ reflect index @-}
{-@ index :: xs:Vec a -> {n:Nat | n < vvlen xs} -> a @-}
index :: Vec a -> Int -> a
index (Cons x _)  0 = x
index (Cons _ xs) n = index xs (n-1)

{-@ reflect fromList @-}
{-@ fromList :: xs:[a] -> {v:Vec a | vvlen v == len xs} @-}
fromList :: [a] -> Vec a
fromList []     = Nil
fromList (x:xs) = x `Cons` fromList xs
