{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module GlobalStore where

-- TODO: swap arguments of GStore

import DSL
import WitnessGeneration
import Semantics (NameValuation)

import qualified Liquid.Data.Map as M

data GlobalStore p b =
  GStore { body  :: b
         , store :: [Assertion p]
         , hints :: NameValuation p -> NameValuation p -- TODO: change to Map?
         }

instance Show b => Show (GlobalStore p b) where
  show = show . body

instance Functor (GlobalStore p) where
  fmap f (GStore body store hints) = GStore (f body) store hints

instance Applicative (GlobalStore p) where
  pure x = GStore x [] (const M.empty)
  GStore f store hints <*> GStore x store' hints' =
    GStore (f x) (store ++ store') (combine hints hints')

instance Monad (GlobalStore p) where
  GStore body store hints >>= f = case f body of
    GStore body' store' hints' ->
      GStore body' (store ++ store') (combine hints hints')

combine :: (NameValuation p -> NameValuation p)
        -> (NameValuation p -> NameValuation p)
        -> (NameValuation p -> NameValuation p)
combine hints1 hints2 ρ =
  let hints1' = hints1 ρ
      hints2' = hints2 (M.union ρ hints1')
      -- the valuation is extended with the hints that came first before
      -- attemping to evaluate the new hints
  in M.union hints1' hints2'


assert :: Assertion p -> GlobalStore p ()
assert x = GStore () [x] (const M.empty)

-- Introduce a hint for witness generation --
-- CAREFUL! This bypasses the type system because the variable 'name' could have
-- been defined with an incompatible type.
define :: String -> (NameValuation p -> Maybe p) -> GlobalStore p ()
define name f = GStore () [] hint where
  hint ρ = case f ρ of
    Nothing    -> M.empty
    Just value -> M.singleton name value

{-@ defineVec :: strs:[String]
              -> (NameValuation p -> Maybe (ListN p (len strs)))
              -> GlobalStore p () @-}
defineVec :: [String] -> (NameValuation p -> Maybe [p]) -> GlobalStore p ()
defineVec names f = GStore () [] hints where
  hints ρ = case f ρ of
    Nothing   -> M.empty
    Just bits -> M.fromList (zip names bits)
