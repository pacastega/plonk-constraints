{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.WitnessGenLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import qualified Data.Set as S

import Utils
import Constraints
import DSL
import Semantics
import WitnessGeneration
import MapLemmas
import Language.Haskell.Liquid.ProofCombinators


{-@ wgBoolean :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
              -> {e:LDSL p (Btwn 0 m) | wfE e && freshE e σ && booleanE e}
              -> {σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e }
              -> { boolean (M.lookup' (outputWire e) σ') } @-}
wgBoolean :: (Eq p, Fractional p) => Int -> NameValuation p -> WireValuation p
          -> LDSL p Int -> WireValuation p -> Proof
wgBoolean m ρ σ e σ' = case e of
  LWIRE  τ i -> elemLemmaSet i value σ ? lookupLemmaSet i σ
    where value = case M.lookup i σ of Just v -> v
  LVAR _ _ i -> trivial

  LUN _ e1 _ -> wgBoolean m ρ σ e1 σ1
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
  LBIN _ e1 e2 _ -> wgBoolean m ρ σ e1 σ1 ? wgBoolean m ρ σ1 e2 σ2
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s

  LEQLC e1 k _ i -> if M.lookup' (outputWire e1) σ1 == k
                   then trivial else trivial
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s


{-@ type MapGE M2 M1 = k:{Int | M.member k M1
                             && S.isSubsetOf (M.keysSet M1) (M.keysSet M2)}
                    -> { M.lookup' k M1 = M.lookup' k M2 } @-}


-- Witness generation never "updates" old keys, only adds new ones.
-- We can think of this as "witnessGenE'(σ,e) ≥ σ".
{-@ wgIncr :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
           -> {e:LDSL p (Btwn 0 m) | wfE e && freshE e σ}
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
  LDIV e1 e2 w i -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
  LUN op e1 i -> wgIncr m ρ σ  e1 σ1 j
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
  LBIN op e1 e2 i -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
  LEQLC e1 k w i -> wgIncr m ρ σ  e1 σ1 j
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s


{-@ coherentEIncr :: m:Nat -> e:LDSL p (Btwn 0 m)
                  -> {σ1:WireValuation p m | closedExpr m σ1 e && coherentE m e σ1}
                  -> {σ2:WireValuation p m | S.isSubsetOf (M.keysSet σ1) (M.keysSet σ2)}
                  -> MapGE σ2 σ1
                  -> { coherentE m e σ2 } @-}
coherentEIncr :: (Eq p, Fractional p) => Int -> LDSL p Int -> WireValuation p
              -> WireValuation p -> (Int -> Proof) -> Proof
coherentEIncr m e σ1 σ2 π = case e of
  LWIRE  _ i -> trivial
  LVAR _ τ i -> case τ of
    TF -> trivial
    TBool -> π i
  LCONST _ i -> π i

  LDIV e1 e2  w i -> coherentEIncr m e1 σ1 σ2 π ? coherentEIncr m e2 σ1 σ2 π
                   ? π (outputWire e1) ? π (outputWire e2) ? π i ? π w
  LUN  op e1    i -> coherentEIncr m e1 σ1 σ2 π ? π (outputWire e1) ? π i
  LBIN op e1 e2 i -> coherentEIncr m e1 σ1 σ2 π ? coherentEIncr m e2 σ1 σ2 π
                   ? π (outputWire e1) ? π (outputWire e2) ? π i
  LEQLC e1 k w i -> coherentEIncr m e1 σ1 σ2 π ? π (outputWire e1) ? π i ? π w
