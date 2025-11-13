{-# LANGUAGE CPP #-}
{-# OPTIONS -Wno-name-shadowing #-}
{-@ LIQUID "--reflection" @-}
module WitnessGeneration (extend, witnessGen, update) where

import Prelude hiding (flip)

import Data.Foldable (foldlM)
import Utils (boolean, zero, one)
import Vec
import DSL
import Semantics

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif


{-@ reflect updateWith @-}
updateWith :: Eq p => Maybe p -> Maybe p -> Maybe p
updateWith Nothing  _        = Nothing
updateWith (Just x) Nothing  = Just x
updateWith (Just x) (Just y) = if x == y then Just x else Nothing

extend :: NameValuation p -> (NameValuation p -> NameValuation p)
       -> NameValuation p
extend valuation hints = M.union valuation (hints valuation)

{-@ reflect witnessGen @-}
{-@ witnessGen :: m:Nat ->
                  [LDSL p (Btwn 0 m)] ->
                  NameValuation p ->
                  Maybe (VecN p m) @-}
witnessGen :: (Eq p, Fractional p) =>
              Int -> [LDSL p Int] -> NameValuation p -> Maybe (Vec p)
witnessGen m programs strNameValuation = toVector m <$> valuation' where
  valuation' = foldlM (update m strNameValuation) M.empty programs

{-@ reflect update @-}
{-@ update :: m:Nat
           -> NameValuation p -> M.Map (Btwn 0 m) p -> LDSL p (Btwn 0 m)
           -> Maybe (M.Map (Btwn 0 m) p) @-}
update :: (Eq p, Fractional p) => Int
       -> NameValuation p -> M.Map Int p -> LDSL p Int -> Maybe (M.Map Int p)
update m _  valuation (LWIRE τ i) = case M.lookup i valuation of
  Nothing -> Nothing -- wire is not defined; TODO: should not happen
  Just value -> case τ of
    TF -> Just valuation -- no restrictions
    TBool -> if boolean value then Just valuation else Nothing
update m sv valuation (LVAR s τ i) = case M.lookup s sv of
  Nothing -> Nothing -- variable is not defined in environment
  Just value -> case τ of
    TF -> Just (M.insert i value valuation)
    TBool -> if boolean value then Just (M.insert i value valuation) else Nothing
update m _  valuation (LCONST x i) = Just (M.insert i x valuation)
update m sv valuation (LDIV p1 p2 w i) =
  case update m sv valuation p1 of
    Nothing -> Nothing
    Just valuation1 -> case update m sv valuation1 p2 of
      Nothing -> Nothing
      Just valuation2 ->
        let i1 = outputWire p1; i2 = outputWire p2
        in case (M.lookup i1 valuation1, M.lookup i2 valuation2)
        of (Just x1, Just x2) ->
             if x2 == 0 then Nothing else
               let valuation3 = M.insert i (x1 / x2) valuation2
               in Just (M.insert w (1 / x2) valuation3)
           _                  -> Nothing
update m sv valuation (LUN op p1 i) =
  case update m sv valuation p1 of
    Nothing -> Nothing
    Just valuation1 ->
      let i1 = outputWire p1
      in case M.lookup i1 valuation1
      of Just x1 ->
           let value = case op of
                 ADDC k1 -> k1 + x1
                 MULC k1 -> k1 * x1
                 NOT -> 1 - x1
                 UnsafeNOT -> 1 - x1
           in Just (M.insert i value valuation1)
         _       -> Nothing
update m sv valuation (LBIN op p1 p2 i) =
  case update m sv valuation p1 of
    Nothing -> Nothing
    Just valuation1 -> case update m sv valuation1 p2 of
      Nothing -> Nothing
      Just valuation2 ->
        let i1 = outputWire p1; i2 = outputWire p2
        in case (M.lookup i1 valuation1, M.lookup i2 valuation2)
        of (Just x1, Just x2) ->
             let value = case op of
                   ADD -> x1 + x2
                   SUB -> x1 - x2
                   MUL -> x1 * x2
                   LINCOMB k1 k2 -> k1*x1 + k2*x2
                   AND -> x1 * x2
                   OR  -> x1 + x2 -   x1*x2
                   XOR -> x1 + x2 - 2*x1*x2
                   UnsafeAND -> x1 * x2
                   UnsafeOR  -> x1 + x2 -   x1*x2
                   UnsafeXOR -> x1 + x2 - 2*x1*x2
             in Just (M.insert i value valuation2)
           _                  -> Nothing

update m sv valuation (LEQLC p1 k w i) =
  case update m sv valuation p1 of
    Nothing -> Nothing
    Just valuation1 ->
      let i1 = outputWire p1
      in case M.lookup i1 valuation1
      of Just x1 -> if x1 == k
           then let valuation2 = M.insert w zero valuation1
                in Just (M.insert i one valuation2)
           else let valuation2 = M.insert w (1/(x1-k)) valuation1
                in Just (M.insert i zero valuation2)
         _       -> Nothing

update m sv valuation (LNZERO p1 w) =
  case update m sv valuation p1 of
    Nothing -> Nothing
    Just valuation1 ->
      let i1 = outputWire p1
      in case M.lookup i1 valuation1
      of Just x1 -> if x1 /= 0 then Just (M.insert w (1/x1) valuation1)
                    else Nothing
         _       -> Nothing
update m sv valuation (LBOOLEAN p1) = update m sv valuation p1
update m sv valuation (LEQA p1 p2) =
  case update m sv valuation p1 of
    Nothing -> Nothing
    Just valuation1 -> update m sv valuation1 p2


{-@ reflect toVector @-}
{-@ toVector :: m:Nat -> M.Map (Btwn 0 m) p -> VecN p m @-}
toVector :: Num p => Int -> M.Map Int p -> Vec p
toVector m valuation = toVector' m m valuation Nil

{-@ reflect toVector' @-}
{-@ toVector' :: m:Nat -> l:Nat -> M.Map (Btwn 0 m) p
              -> {v:Vec p | vvlen v = (m-l)}
              -> VecN p m / [l] @-}
toVector' :: Num p => Int -> Int -> M.Map Int p -> Vec p -> Vec p
toVector' m 0 val acc = acc
toVector' m l val acc = toVector' m (l-1) val
                         (Cons (M.findWithDefault zero (l-1) val) acc)



-- -- TODO: ‘ensure (/= 0)’ should work for ‘x2’ in the case of ‘LDIV’ above
-- {-@ ensure :: p:(a -> Bool) -> x:a ->
--               {v:Maybe {w:a | p w} | v = (if (p x) then (Just x)
--                                                    else Nothing)} @-}
ensure :: (a -> Bool) -> a -> Maybe a
ensure p x = if p x then Just x else Nothing
