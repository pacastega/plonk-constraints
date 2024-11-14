{-@ LIQUID "--reflection" @-}
module GlobalStore where

-- import Control.Monad.Writer
-- type GlobalStore a b = Writer [(String, b)] a

-- TODO: swap arguments of GStore

data GlobalStore a b = GStore b [a] deriving Show

instance Functor (GlobalStore a) where
  fmap f (GStore val res) = GStore (f val) res

instance Applicative (GlobalStore a) where
  pure x = GStore x []
  GStore f res <*> GStore x res' = GStore (f x) (res ++ res')

instance Monad (GlobalStore a) where
  GStore val res >>= f = case f val of
    GStore val' res' -> GStore val' (res ++ res')

{-@ measure body @-}
body :: GlobalStore a b -> b
body (GStore x _) = x

assert :: a -> GlobalStore a ()
assert x = GStore () [x]
