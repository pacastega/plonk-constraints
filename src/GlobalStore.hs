{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module GlobalStore where

-- TODO: swap arguments of GStore

import DSL
import WitnessGeneration

import qualified Data.Map as M

data GlobalStore p b =
  GStore { body  :: b
         , store :: [Assertion p]
         , hints :: ValuationRefl p -> [(String, p)] -- TODO: change to Map?
         }

instance Show b => Show (GlobalStore p b) where
  show = show . body

instance Functor (GlobalStore p) where
  fmap f (GStore body store hints) = GStore (f body) store hints

instance Applicative (GlobalStore p) where
  pure x = GStore x [] (const [])
  GStore f store hints <*> GStore x store' hints' =
    GStore (f x) (store ++ store') (combine hints hints')

instance Monad (GlobalStore p) where
  GStore body store hints >>= f = case f body of
    GStore body' store' hints' ->
      GStore body' (store ++ store') (combine hints hints')

combine :: (ValuationRefl p -> [(String, p)]) -> (ValuationRefl p -> [(String, p)])
        -> (ValuationRefl p -> [(String, p)])
combine hints1 hints2 valuation =
  let hints1' = hints1 (valuation)
      hints2' = hints2 (valuation ++ hints1')
      -- the valuation is extended with the hints that came first before
      -- attemping to evaluate the new hints
  in hints1' ++ hints2'


assert :: Assertion p -> GlobalStore p ()
assert x = GStore () [x] (const [])

-- Introduce a hint for witness generation --
-- CAREFUL! This bypasses the type system because the variable 'name' could have
-- been defined with an incompatible type.
define :: String -> (ValuationRefl p -> Maybe p) -> GlobalStore p ()
define name f = GStore () [] hint where
  hint valuation = case f valuation of
    Nothing    -> []
    Just value -> [(name, value)]

{-@ defineVec :: strs:[String]
              -> (ValuationRefl p -> Maybe (ListN p (len strs)))
              -> GlobalStore p () @-}
defineVec :: [String] -> (ValuationRefl p -> Maybe [p]) -> GlobalStore p ()
defineVec names f = GStore () [] hints where
  hints valuation = case f valuation of
    Nothing   -> []
    Just bits -> zip names bits
