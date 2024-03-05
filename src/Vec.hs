{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Vec where

data RVec a = Nil | Cons a (RVec a)
  deriving Show


{-@ data RVec [vvlen] a = Nil | Cons {xVec:: a, xsVec:: RVec a} @-}

infixr 5 `Cons`

{-@ vvlen :: RVec a -> Nat @-}
vvlen :: RVec a -> Int
vvlen Nil         = 0
vvlen (Cons _ xs) = 1 + vvlen xs

{-@ measure vvlen @-}

-- {-@ impossible :: {v:String | False} -> a @-}
-- impossible :: String -> a
-- impossible = error

{-@ reflect index @-}
{-@ index :: xs:RVec a -> {n:Nat | n < vvlen xs} -> a @-}
index :: RVec a -> Int -> a
-- index Nil         _ = impossible "The list must be non-empty"
index (Cons x _)  0 = x
index (Cons _ xs) n = index xs (n-1)

{-@ fromList :: xs:[a] -> {v:RVec a | vvlen v == len xs} @-}
fromList :: [a] -> RVec a
fromList []     = Nil
fromList (x:xs) = x `Cons` fromList xs
