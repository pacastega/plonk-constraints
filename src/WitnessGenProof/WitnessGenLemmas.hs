{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.WitnessGenLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import TypeAliases
import Utils
import DSL
import Semantics
import WitnessGeneration
import MapLemmas
import Language.Haskell.Liquid.ProofCombinators


{-@ wgLemma :: m:Nat -> m':{Nat | m' >= m}
            -> ρ:NameValuation p -> σ:WireValuation p m
            -> e:{TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ}
            -> { witnessGenE' m ρ σ e == witnessGenE' m' ρ σ e } @-}
wgLemma :: (Eq p, Fractional p) => Int -> Int
        -> NameValuation p -> WireValuation p -> LDSL p Int -> Proof
wgLemma m m' ρ σ e = case e of
  LWIRE {} -> trivial
  LVAR {} -> trivial
  LCONST {} -> trivial
  LBOOL  {} -> trivial

  LDIV e1 e2 _ _ -> wgLemma m m' ρ σ e1 ? case witnessGenE' m ρ σ e1 of
    Nothing -> trivial; Just σ1 -> wgLemma m m' ρ σ1 e2

  LUN _ e1 _ -> wgLemma m m' ρ σ e1
  LBIN _ e1 e2 _ -> wgLemma m m' ρ σ e1 ? case witnessGenE' m ρ σ e1 of
    Nothing -> trivial; Just σ1 -> wgLemma m m' ρ σ1 e2

  LBoolToF e1 -> wgLemma m m' ρ σ e1
  LEQLC e1 _ _ _ -> wgLemma m m' ρ σ e1

  LNIL _ ->  trivial
  LCONS e1 e2 -> wgLemma m m' ρ σ e1 ? case witnessGenE' m ρ σ e1 of
    Nothing -> trivial; Just σ1 -> wgLemma m m' ρ σ1 e2


{-@ wgBoolean :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
              -> {e:TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ && booleanE e}
              -> {σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e }
              -> { boolean (M.lookup' (outputWire e) σ') } @-}
wgBoolean :: (Eq p, Fractional p) => Int -> NameValuation p -> WireValuation p
          -> LDSL p Int -> WireValuation p -> Proof
wgBoolean m ρ σ e σ' = case e of
  LWIRE  τ i -> elementLemma i value σ ? lookupLemma i σ
              ? witnessGenE' m ρ σ (LWIRE τ i)
    where value = case M.lookup i σ of Just v -> v
  LVAR _ _ i -> trivial
  LBOOL  {} -> trivial

  LUN _ e1 _ -> wgBoolean m ρ σ e1 σ1
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
  LBIN _ e1 e2 _ -> wgBoolean m ρ σ e1 σ1 ? wgBoolean m ρ σ1 e2 σ2
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s

  LBoolToF e1 -> wgBoolean m ρ σ e1 σ'
  LEQLC e1 k _ i -> if M.lookup' (outputWire e1) σ1 == k
                   then trivial else trivial
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s


-- Witness generation never "updates" old keys, only adds new ones.
-- We can think of this as "witnessGenE'(σ,e) ≥ σ".
{-@ wgIncr :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
           -> {e:TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ}
           -> {σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
           -> MapGE σ' σ @-}
wgIncr :: (Eq p, Fractional p) => Int -> NameValuation p -> WireValuation p
       -> LDSL p Int -> WireValuation p -> (Int -> Proof)
wgIncr m ρ σ e σ' j = case e of
  LWIRE  τ i -> trivial ? witnessGenE' m ρ σ e
  LVAR s τ i -> case τ of
    TF -> trivial
    TBool -> trivial
  LCONST x i -> trivial
  LBOOL  b i -> trivial
  LDIV e1 e2 w i -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
  LUN op e1 i -> wgIncr m ρ σ  e1 σ1 j
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
  LBIN op e1 e2 i -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
  LBoolToF e1 -> wgIncr m ρ σ e1 σ' j
  LEQLC e1 k w i -> wgIncr m ρ σ  e1 σ1 j
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
  LNIL _ -> trivial
  LCONS e1 e2 -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s


{-@ wgClosed :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
               -> e':{TypedLDSL p (Btwn 0 m) | wfE e' && freshE e' σ}
               -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}
               -> { closedExpr m σ' e' } @-}
wgClosed :: (Ord p, Fractional p) => Int -> NameValuation p -> WireValuation p
           -> LDSL p Int -> WireValuation p -> Proof
wgClosed m ρ σ e' σ' = case witnessGenE' m ρ σ e' of Just _ -> trivial
