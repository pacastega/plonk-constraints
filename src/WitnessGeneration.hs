{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# OPTIONS -Wno-name-shadowing #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGeneration where

import Prelude hiding (flip)

import TypeAliases
import Utils
import Vec
import DSL

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import MapLemmas
import Language.Haskell.Liquid.ProofCombinators

extend :: NameValuation p -> (NameValuation p -> NameValuation p)
       -> NameValuation p
extend ρ hints = M.union ρ (hints ρ)


{-@ reflect freshE @-}
freshE :: (Ord i) => LDSL p i -> M.Map i p -> Bool
freshE e σ = disjoint (wiresE e) (M.keysSet σ)

{-@ inline freshA @-}
freshA :: (Ord i) => LAss p i -> M.Map i p -> Bool
freshA a σ = disjoint (wiresA a) (M.keysSet σ)

{-@ inline freshProgram @-}
freshProgram :: (Ord i) => LProg p i -> M.Map i p -> Bool
freshProgram pr σ = disjoint (wires pr) (M.keysSet σ)

{-@ inline freshPrograms @-}
freshPrograms :: (Ord i) => [LProg p i] -> M.Map i p -> Bool
freshPrograms ps σ = disjoint (wiress ps) (M.keysSet σ)

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
                               M.keysSet σ' = S.union (M.keysSet σ) (wiress ps)}) @-}
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
                            M.keysSet σ' = S.union (M.keysSet σ) (wires pr)}) @-}
witnessGen' :: (Eq p, Fractional p) => Int
            -> NameValuation p -> WireValuation p -> LProg p Int
            -> Maybe (WireValuation p)
witnessGen' m ρ σ (LExpr e) = freshE e σ ?? witnessGenE' m ρ σ e
witnessGen' m ρ σ (LAss a) = freshA a σ ?? witnessGenA' m ρ σ a

{-@ reflect witnessGenE' @-}
{-@ witnessGenE' :: m:Nat
                 -> NameValuation p -> σ:WireValuation p m
                 -> {e:TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ}
                 -> Maybe ({σ':WireValuation p m | closedExpr m σ' e &&
                             M.keysSet σ' = S.union (M.keysSet σ) (wiresE e)}) @-}
witnessGenE' :: (Eq p, Fractional p) => Int
             -> NameValuation p -> WireValuation p -> LDSL p Int
             -> Maybe (WireValuation p)
witnessGenE' m ρ σ e = case e of
  LWIRE τ i -> case M.lookup i σ of
    Nothing -> Nothing -- wire hasn't appeared before
    Just value -> elementLemma i value σ ?? case τ of
      TF -> Just σ -- no restrictions
      TBool -> if boolean value -- Always true, but that's challenging to prove.
               then Just σ -- Leave this just to prove the booleanity invariant.
               else Nothing
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
      Just σ2 -> if x2 == 0 then Nothing else
                   let σ3 = M.insert i (x1 / x2) σ2
                   in Just (M.insert w (1 / x2) σ3)
        where x1 = M.lookup' (outputWire p1) σ1
              x2 = M.lookup' (outputWire p2) σ2
  LUN op p1 i -> case witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> Just (M.insert i value σ1)
      where x1 = M.lookup' (outputWire p1) σ1
            value = case op of
              ADDC k1 -> k1 + x1
              MULC k1 -> k1 * x1
              NOT -> 1 - x1
              UnsafeNOT -> 1 - x1
  LBIN op p1 p2 i -> case witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> case witnessGenE' m ρ σ1 p2 of
      Nothing -> Nothing
      Just σ2 -> Just (M.insert i value σ2)
        where x1 = M.lookup' (outputWire p1) σ1
              x2 = M.lookup' (outputWire p2) σ2
              value = case op of
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

  LEQLC p1 k w i -> case witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> Just (M.insert i value (M.insert w witness σ1))
      where x1 = M.lookup' (outputWire p1) σ1
            value = if x1 == k then one else zero -- think True or False
            witness = if x1 == k then zero else 1/(x1-k)

  LNIL _ -> Just σ
  LCONS p1 p2 -> case witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> witnessGenE' m ρ σ1 p2

{-@ reflect witnessGenA' @-}
{-@ witnessGenA' :: m:Nat
                 -> NameValuation p -> σ:WireValuation p m
                 -> {a:LAss p (Btwn 0 m) | wfA a && freshA a σ}
                 -> Maybe ({σ':WireValuation p m |
                             M.keysSet σ' = S.union (M.keysSet σ) (wiresA a)}) @-}
witnessGenA' :: (Eq p, Fractional p) => Int
             -> NameValuation p -> WireValuation p -> LAss p Int
             -> Maybe (WireValuation p)
witnessGenA' m ρ σ a = case a of
  LNZERO p1 w -> scalar' p1 ?? case witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> if x1 /= 0 then Just (M.insert w (1/x1) σ1) else Nothing
      where x1 = M.lookup' (outputWire p1) σ1
  LBOOLEAN p1 -> scalar' p1 ?? witnessGenE' m ρ σ p1
  LEQA p1 p2 -> case scalar' p1 ?? witnessGenE' m ρ σ p1 of
    Nothing -> Nothing
    Just σ1 -> scalar' p2 ?? witnessGenE' m ρ σ1 p2
