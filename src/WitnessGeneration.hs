{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# OPTIONS -Wno-name-shadowing #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGeneration where

import Prelude hiding (flip)

import Constraints
import Data.Foldable (foldlM)
import Utils
import Vec
import DSL
import Semantics

import qualified Data.Set as S

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


{-@ inline freshE @-}
freshE :: (Ord i) => LDSL p i -> M.Map i p -> Bool
freshE e σ = disjoint (wiresE e) (M.keySet σ)

{-@ inline freshA @-}
freshA :: (Ord i) => LAss p i -> M.Map i p -> Bool
freshA a σ = disjoint (wiresA a) (M.keySet σ)

{-@ inline freshProgram @-}
freshProgram :: (Ord i) => LProg p i -> M.Map i p -> Bool
freshProgram pr σ = disjoint (wires pr) (M.keySet σ)

{-@ inline freshPrograms @-}
freshPrograms :: (Ord i) => [LProg p i] -> M.Map i p -> Bool
freshPrograms ps σ = disjoint (allWires ps) (M.keySet σ)

{-@ reflect witnessGen @-}
{-@ witnessGen :: m:Nat
               -> {ps:[LProg p (Btwn 0 m)] | wfs ps}
               -> NameValuation p
               -> Maybe (WireValuation p m) @-}
witnessGen :: forall p. (Eq p, Fractional p) => Int
           -> [LProg p Int] -> NameValuation p -> Maybe (WireValuation p)
witnessGen m programs ρ = witnessGenStar m ρ M.empty programs

{-@ reflect witnessGenStar @-}
{-@ witnessGenStar :: m:Nat
                   -> NameValuation p
                   -> σ:WireValuation p m
                   -> ps:{[LProg p (Btwn 0 m)] | wfs ps && freshPrograms ps σ}
                   -> Maybe ({σ':WireValuation p m |
                               M.keySet σ' = S.union (M.keySet σ) (allWires ps)}) @-}
witnessGenStar :: (Eq p, Fractional p) => Int
               -> NameValuation p -> WireValuation p -> [LProg p Int]
               -> Maybe (WireValuation p)
witnessGenStar m ρ σ [] = Just σ
witnessGenStar m ρ σ programs@(p:ps) = case witnessGen' m ρ σ p of
  Nothing -> Nothing
  Just σ' -> wfs programs ?? witnessGenStar m ρ σ' ps


{-@ reflect witnessGen' @-}
{-@ witnessGen' :: m:Nat
                -> NameValuation p -> σ:WireValuation p m
                -> {pr:LProg p (Btwn 0 m) | wf pr && freshProgram pr σ}
                -> Maybe ({σ':WireValuation p m |
                            M.keySet σ' = S.union (M.keySet σ) (wires pr)}) @-}
witnessGen' :: (Eq p, Fractional p) => Int
            -> NameValuation p -> WireValuation p -> LProg p Int
            -> Maybe (WireValuation p)
witnessGen' m ρ σ (LExpr e) = freshE e σ ?? witnessGenE' m ρ σ e
witnessGen' m ρ σ (LAss a) = freshA a σ ?? witnessGenA' m ρ σ a

{-@ reflect witnessGenE' @-}
{-@ witnessGenE' :: m:Nat
                 -> NameValuation p -> σ:WireValuation p m
                 -> {e:LDSL p (Btwn 0 m) | wfE e && freshE e σ}
                 -> Maybe ({σ':WireValuation p m |
                             M.keySet σ' = S.union (M.keySet σ) (wiresE e)}) @-}
witnessGenE' :: (Eq p, Fractional p) => Int
             -> NameValuation p -> WireValuation p -> LDSL p Int
             -> Maybe (WireValuation p)
witnessGenE' m ρ σ e = case e of
  LWIRE τ i -> case M.lookup i σ of
    Nothing -> Nothing -- wire is not defined
    Just value -> case τ of
      TF -> Just σ -- no restrictions
      TBool -> if boolean value then Just σ else Nothing
  LVAR s τ i -> case M.lookup s ρ of
    Nothing -> Nothing -- variable is not defined in environment
    Just value -> case τ of
      TF -> Just (M.insert i value σ)
      TBool -> if boolean value then Just (M.insert i value σ) else Nothing
  LCONST x i -> Just (M.insert i x σ)
  LDIV p1 p2 w i -> case witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> case witnessGenE' m ρ σ1 p2 of
      Nothing -> Nothing
      Just σ2 ->
        let i1 = outputWire p1; i2 = outputWire p2
        in case (M.lookup i1 σ1, M.lookup i2 σ2)
        of (Just x1, Just x2) ->
             if x2 == 0 then Nothing else
               let σ3 = M.insert i (x1 / x2) σ2
               in Just (M.insert w (1 / x2) σ3)
           _                  -> Nothing
  LUN op p1 i -> case witnessGenE' m ρ σ p1 of
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
  LBIN op p1 p2 i -> case witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> case witnessGenE' m ρ σ1 p2 of
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

  LEQLC p1 k w i -> case witnessGenE' m ρ σ p1 of
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

{-@ reflect witnessGenA' @-}
{-@ witnessGenA' :: m:Nat
                 -> NameValuation p -> σ:WireValuation p m
                 -> {a:LAss p (Btwn 0 m) | wfA a && freshA a σ}
                 -> Maybe ({σ':WireValuation p m |
                             M.keySet σ' = S.union (M.keySet σ) (wiresA a)}) @-}
witnessGenA' :: (Eq p, Fractional p) => Int
             -> NameValuation p -> WireValuation p -> LAss p Int
             -> Maybe (WireValuation p)
witnessGenA' m ρ σ a = case a of
  LNZERO p1 w -> case witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 ->
      let i1 = outputWire p1
      in case M.lookup i1 σ1
      of Just x1 -> if x1 /= 0 then Just (M.insert w (1/x1) σ1)
                    else Nothing
         _       -> Nothing
  LBOOLEAN p1 -> witnessGenE' m ρ σ p1
  LEQA p1 p2 -> case witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> witnessGenE' m ρ σ1 p2
