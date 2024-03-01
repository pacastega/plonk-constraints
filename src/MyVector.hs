module MyVector (index) where

data MyVector a = Nil | Cons a (MyVector a)
  deriving Show

infixr 5 `Cons`

{-@ len :: MyVector a -> Nat @-}
len :: MyVector a -> Int
len Nil         = 0
len (Cons _ xs) = 1 + len xs

{-@ measure len @-}
{-@ data MyVector [len] @-}

-- TODO: Is this necessary to make LH realise Nil can’t be used in the
-- definitions below?
{-@ impossible :: {s:String | False} -> a @-}
impossible :: String -> a
impossible = error

{-@ head :: {v:MyVector a | len v > 0} -> a @-}
head :: MyVector a -> a
head Nil        = impossible "Nil has zero length"
head (Cons x _) = x

{-@ tail :: {v:MyVector a | len v > 0} -> MyVector a @-}
tail :: MyVector a -> MyVector a
tail Nil         = impossible "Nil has zero length"
tail (Cons _ xs) = xs

{-@ index :: xs:MyVector a -> {n:Nat | n < len xs} -> a @-}
index :: MyVector a -> Int -> a
index Nil         _ = impossible "The list must be non-empty"
index (Cons x _)  0 = x
index (Cons _ xs) n = index xs (n-1)
