{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module PlinkST where

import DSL
import WitnessGeneration
import Semantics (NameValuation)

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

data PlinkST p b =
  PlinkST { body  :: b
          , store :: [Assertion p]
          , hints :: NameValuation p -> NameValuation p
          }

instance Show b => Show (PlinkST p b) where
  show = show . body

instance Functor (PlinkST p) where
  fmap f (PlinkST body store hints) = PlinkST (f body) store hints

instance Applicative (PlinkST p) where
  pure x = PlinkST x [] (const M.empty)
  PlinkST f store hints <*> PlinkST x store' hints' =
    PlinkST (f x) (store ++ store') (combine hints hints')

instance Monad (PlinkST p) where
  PlinkST body store hints >>= f = case f body of
    PlinkST body' store' hints' ->
      PlinkST body' (store ++ store') (combine hints hints')

combine :: (NameValuation p -> NameValuation p)
        -> (NameValuation p -> NameValuation p)
        -> (NameValuation p -> NameValuation p)
combine hints1 hints2 ρ =
  let hints1' = hints1 ρ
      hints2' = hints2 (M.union ρ hints1')
      -- the valuation is extended with the hints that came first before
      -- attemping to evaluate the new hints
  in M.union hints1' hints2'


assert :: Assertion p -> PlinkST p ()
assert x = PlinkST () [x] (const M.empty)

-- Introduce a hint for witness generation --
-- CAREFUL! This bypasses the type system because the variable 'name' could have
-- been defined with an incompatible type.
define :: String -> (NameValuation p -> Maybe p) -> PlinkST p ()
define name f = PlinkST () [] hint where
  hint ρ = case f ρ of
    Nothing    -> M.empty
    Just value -> M.singleton name value

{-@ defineVec :: strs:[String]
              -> (NameValuation p -> Maybe (ListN p (len strs)))
              -> PlinkST p () @-}
defineVec :: [String] -> (NameValuation p -> Maybe [p]) -> PlinkST p ()
defineVec names f = PlinkST () [] hints where
  hints ρ = case f ρ of
    Nothing   -> M.empty
    Just bits -> M.fromList (zip names bits)
