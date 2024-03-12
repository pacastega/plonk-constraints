{-@ LIQUID "--reflection" @-}
module Vec where

{-@ data Vec  a  = Nil | Cons {vx :: a,  vxs :: Vec a} @-}
data Vec a = Nil | Cons a (Vec a)

instance Show a => Show (Vec a) where
  show v = "<" ++ show_ v ++ ">" where
    show_ (Nil)        = " "
    show_ (Cons x Nil) = show x
    show_ (Cons x xs)  = show x ++ "," ++ show_ xs

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

{-@ singleton :: a -> {v:Vec a | vvlen v == 1} @-}
singleton :: a -> Vec a
singleton = (`Cons` Nil)

{-@ append :: xs:Vec a -> ys:Vec a ->
              {v:Vec a | vvlen v == vvlen xs + vvlen ys} @-}
append :: Vec a -> Vec a -> Vec a
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)
