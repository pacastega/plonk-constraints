module MyVector where

data MyVector a = Nil | Cons a (MyVector a)

{-@ len :: MyVector a -> Nat @-}
len :: MyVector a -> Int
len Nil         = 0
len (Cons _ xs) = 1 + len xs

{-@ measure len @-}
{-@ data MyVector [len] @-}

{-@ index :: xs:MyVector a -> {n:Nat | n < len xs} -> a @-}
index :: MyVector a -> Int -> a
index (Cons x _)  0 = x
index (Cons _ xs) n = index xs (n-1)
