module Vec (Vec (..), index, fromList) where

data Vec a = Nil | Cons a (Vec a)
  deriving Show

infixr 5 `Cons`

{-@ len :: Vec a -> Nat @-}
len :: Vec a -> Int
len Nil         = 0
len (Cons _ xs) = 1 + len xs

{-@ measure len @-}
{-@ data Vec [len] @-}

-- TODO: Is this necessary to make LH realise Nil can’t be used in the
-- definitions below?
{-@ impossible :: {s:String | False} -> a @-}
impossible :: String -> a
impossible = error

{-@ head :: {v:Vec a | len v > 0} -> a @-}
head :: Vec a -> a
head Nil        = impossible "Nil has zero length"
head (Cons x _) = x

{-@ tail :: {v:Vec a | len v > 0} -> Vec a @-}
tail :: Vec a -> Vec a
tail Nil         = impossible "Nil has zero length"
tail (Cons _ xs) = xs

{-@ index :: xs:Vec a -> {n:Nat | n < len xs} -> a @-}
index :: Vec a -> Int -> a
index Nil         _ = impossible "The list must be non-empty"
index (Cons x _)  0 = x
index (Cons _ xs) n = index xs (n-1)

{-@ fromList :: xs:[a] -> {v:Vec a | len v == len xs} @-}
fromList :: [a] -> Vec a
fromList []     = Nil
fromList (x:xs) = x `Cons` fromList xs
