{-# LANGUAGE CPP #-}
{-# OPTIONS -Wno-name-shadowing #-}
{-@ LIQUID "--reflection" @-}
module WitnessGeneration (extend, witnessGen, witnessGen') where

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
extend ρ hints = M.union ρ (hints ρ)

{-@ reflect witnessGen @-}
{-@ witnessGen :: m:Nat
               -> [LDSL p (Btwn 0 m)]
               -> NameValuation p
               -> Maybe (VecN p m) @-}
witnessGen :: (Eq p, Fractional p) =>
              Int -> [LDSL p Int] -> NameValuation p -> Maybe (Vec p)
witnessGen m programs ρ = toVector m <$> σ where
  σ = foldlM (witnessGen' m ρ) M.empty programs

{-@ reflect witnessGen' @-}
{-@ witnessGen' :: m:Nat
                -> NameValuation p -> M.Map (Btwn 0 m) p -> LDSL p (Btwn 0 m)
                -> Maybe (M.Map (Btwn 0 m) p) @-}
witnessGen' :: (Eq p, Fractional p) => Int
    -> NameValuation p -> M.Map Int p -> LDSL p Int -> Maybe (M.Map Int p)
witnessGen' m _ σ (LWIRE τ i) = case M.lookup i σ of
  Nothing -> Nothing -- wire is not defined
  Just value -> case τ of
    TF -> Just σ -- no restrictions
    TBool -> if boolean value then Just σ else Nothing
witnessGen' m ρ σ (LVAR s τ i) = case M.lookup s ρ of
  Nothing -> Nothing -- variable is not defined in environment
  Just value -> case τ of
    TF -> Just (M.insert i value σ)
    TBool -> if boolean value then Just (M.insert i value σ) else Nothing
witnessGen' m _  σ (LCONST x i) = Just (M.insert i x σ)
witnessGen' m ρ σ (LDIV p1 p2 w i) =
  case witnessGen' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> case witnessGen' m ρ σ1 p2 of
      Nothing -> Nothing
      Just σ2 ->
        let i1 = outputWire p1; i2 = outputWire p2
        in case (M.lookup i1 σ1, M.lookup i2 σ2)
        of (Just x1, Just x2) ->
             if x2 == 0 then Nothing else
               let σ3 = M.insert i (x1 / x2) σ2
               in Just (M.insert w (1 / x2) σ3)
           _                  -> Nothing
witnessGen' m ρ σ (LUN op p1 i) =
  case witnessGen' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 ->
      let i1 = outputWire p1
      in case M.lookup i1 σ1
      of Just x1 ->
           let value = case op of
                 ADDC k1 -> k1 + x1
                 MULC k1 -> k1 * x1
                 NOT -> 1 - x1
                 UnsafeNOT -> 1 - x1
           in Just (M.insert i value σ1)
         _       -> Nothing
witnessGen' m ρ σ (LBIN op p1 p2 i) =
  case witnessGen' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> case witnessGen' m ρ σ1 p2 of
      Nothing -> Nothing
      Just σ2 ->
        let i1 = outputWire p1; i2 = outputWire p2
        in case (M.lookup i1 σ1, M.lookup i2 σ2)
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
             in Just (M.insert i value σ2)
           _                  -> Nothing

witnessGen' m ρ σ (LEQLC p1 k w i) =
  case witnessGen' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 ->
      let i1 = outputWire p1
      in case M.lookup i1 σ1
      of Just x1 -> if x1 == k
           then let σ2 = M.insert w zero σ1
                in Just (M.insert i one σ2)
           else let σ2 = M.insert w (1/(x1-k)) σ1
                in Just (M.insert i zero σ2)
         _       -> Nothing

witnessGen' m ρ σ (LNZERO p1 w) =
  case witnessGen' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 ->
      let i1 = outputWire p1
      in case M.lookup i1 σ1
      of Just x1 -> if x1 /= 0 then Just (M.insert w (1/x1) σ1)
                    else Nothing
         _       -> Nothing
witnessGen' m ρ σ (LBOOLEAN p1) = witnessGen' m ρ σ p1
witnessGen' m ρ σ (LEQA p1 p2) =
  case witnessGen' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> witnessGen' m ρ σ1 p2


{-@ reflect toVector @-}
{-@ toVector :: m:Nat -> M.Map (Btwn 0 m) p -> VecN p m @-}
toVector :: Num p => Int -> M.Map Int p -> Vec p
toVector m σ = toVector' m m σ Nil

{-@ reflect toVector' @-}
{-@ toVector' :: m:Nat -> l:Nat -> M.Map (Btwn 0 m) p
              -> {v:Vec p | vvlen v = (m-l)}
              -> VecN p m / [l] @-}
toVector' :: Num p => Int -> Int -> M.Map Int p -> Vec p -> Vec p
toVector' m 0 val acc = acc
toVector' m l val acc = toVector' m (l-1) val
                         (Cons (M.findWithDefault zero (l-1) val) acc)
