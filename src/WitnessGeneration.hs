{-# OPTIONS -Wno-name-shadowing #-}
{-@ LIQUID "--reflection" @-}
module WitnessGeneration (witnessGen) where

import Prelude hiding (lookup)

import Vec
import DSL
import Data.Map (Map, alter, lookup, findWithDefault)


updateWith :: Eq p => Maybe p -> Maybe p -> Maybe p
updateWith Nothing  _        = Nothing
updateWith (Just x) Nothing  = Just x
updateWith (Just x) (Just y) = if x == y then Just x else Nothing


{-@ witnessGen :: m:Nat1 ->
                  program:LDSL p (Btwn 0 m) ->
                  Map ({v:Btwn 0 m | True}) p ->
                  VecN p m @-}
witnessGen :: (Eq p, Num p) => Int -> LDSL p Int -> Map Int p -> Vec p
witnessGen m program valuation = toVector m $ update program valuation where
    update (LWIRE _) valuation = valuation
    update (LCONST x i) valuation = alter (updateWith (Just x)) i valuation
    update (LADD p1 p2 i) valuation = alter (updateWith sum) i valuation' where
      valuation' = update p2 $ update p1 valuation
      x1 = lookup (outputWire p1) valuation'
      x2 = lookup (outputWire p2) valuation'
      sum = (+) <$> x1 <*> x2
    update (LMUL p1 p2 i) valuation = alter (updateWith mult) i valuation' where
      valuation' = update p2 $ update p1 valuation
      x1 = lookup (outputWire p1) valuation'
      x2 = lookup (outputWire p2) valuation'
      mult = (*) <$> x1 <*> x2


{-@ toVector :: m:Nat -> Map (Btwn 0 m) p -> VecN p m @-}
toVector :: Num p => Int -> Map Int p -> Vec p
toVector m valuation = aux m Nil where
  {-@ aux :: l:Nat -> acc:{Vec p | vvlen acc = m-l} -> VecN p m @-}
  aux 0 acc = acc
  aux l acc = aux (l-1) (Cons (findWithDefault 0 (l-1) valuation) acc)
