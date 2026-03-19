{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--fast" @-}
module WitnessGenProof.Soundness where

import Constraints
import TypeAliases
import DSL
import Semantics
import WitnessGeneration

import Utils

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import WitnessGenProof.WitnessGenLemmas
import WitnessGenProof.SoundnessBase

import Language.Haskell.Liquid.ProofCombinators


{-@ wgSoundE :: m:Nat
             -> ρ:NameValuation p
             -> σ:WireValuation p m
             -> {e:TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ}
             -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
             -> { coherentE m e σ' } @-}
wgSoundE :: (Eq p, Fractional p)
         => Int -> NameValuation p -> WireValuation p -> LDSL p Int
         -> WireValuation p -> Proof
wgSoundE m ρ σ e σ' = case e of
  LWIRE τ i -> wgSoundWire m ρ σ τ i σ'
  LVAR s τ i -> wgSoundVar m ρ σ s τ i σ'
  LCONST x i -> wgSoundConst m ρ σ x i σ'

  LDIV e1 e2 w i -> wgSoundE m ρ σ e1 σ1        -- σ1 ⊢ e1 (by IH)
                  ? coherentEIncr m e1 σ1 σ2 π1 -- σ2 ⊢ e1 (since σ2 ≥ σ1)
                  ? coherentEIncr m e1 σ2 σ' π2 -- σ' ⊢ e1 (since σ' ≥ σ2)

                  ? wgSoundE m ρ σ1 e2 σ2       -- σ2 ⊢ e2 (by IH)
                  ? coherentEIncr m e2 σ2 σ' π2 -- σ' ⊢ e2 (since σ' ≥ σ2)

                  ? π1 (outputWire e1) -- σ2[i1] == σ1[i1] (since σ2 ≥ σ1)
                  ? π2 (outputWire e1) -- σ'[i1] == σ1[i1] (since σ' ≥ σ2)
                  ? π2 (outputWire e2) -- σ'[i2] == σ2[i2] (since σ' ≥ σ2)

                  ? liquidAssert (v1 == M.lookup' (outputWire e1) σ')
                  ? liquidAssert (v2 == M.lookup' (outputWire e2) σ')

                  ? liquidAssert (vi == v1 / v2) -- true
                  ? liquidAssert (vw == 1 / v2)  -- true
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s

          v1 = M.lookup' (outputWire e1) σ1
          v2 = M.lookup' (outputWire e2) σ2
          vw = M.lookup' w σ'
          vi = M.lookup' i σ'

          {-@ π1 :: MapGE σ2 σ1 @-}
          π1 :: Int -> Proof
          π1 j = wgIncr m ρ σ1 e2 σ2 j

          {-@ π2 :: MapGE σ' σ2 @-}
          π2 :: Int -> Proof
          π2 j = liquidAssert (j /= i && j /= w) ? M.member j σ2 ? M.lookup' j σ'

  LUN op e1 i -> case op of
    ADDC k -> proof; MULC k -> proof; UnsafeNOT -> proof;
    NOT -> proof ? wgBoolean m ρ σ e1 σ1;
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
          proof = wgSoundE m ρ σ e1 σ1
                ? coherentEIncr m e1 σ1 σ' (\j -> trivial ? M.member j σ1
                                                          ? M.lookup' j σ')

  LBIN op e1 e2 i -> case op of
    ADD -> proof; SUB -> proof; MUL -> proof; LINCOMB _ _ -> proof;
    AND -> proof ? wgBoolean m ρ σ e1 σ1 ? wgBoolean m ρ σ1 e2 σ2;
    OR  -> proof ? wgBoolean m ρ σ e1 σ1 ? wgBoolean m ρ σ1 e2 σ2;
    XOR -> proof ? wgBoolean m ρ σ e1 σ1 ? wgBoolean m ρ σ1 e2 σ2;
    UnsafeAND -> proof;
    UnsafeOR  -> proof;
    UnsafeXOR -> proof;
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
          proof = wgSoundE m ρ σ e1 σ1        -- σ1 ⊢ e1 (by IH)
                ? coherentEIncr m e1 σ1 σ2 π1 -- σ2 ⊢ e1 (since σ2 ≥ σ1)
                ? coherentEIncr m e1 σ2 σ' π2 -- σ' ⊢ e1 (since σ' ≥ σ2)

                ? wgSoundE m ρ σ1 e2 σ2       -- σ2 ⊢ e2 (by IH)
                ? coherentEIncr m e2 σ2 σ' π2 -- σ' ⊢ e2 (since σ' ≥ σ2)

                ? π1 (outputWire e1) -- σ2[i1] == σ1[i1] (since σ2 ≥ σ1)

          {-@ π1 :: MapGE σ2 σ1 @-}
          π1 :: Int -> Proof
          π1 j = wgIncr m ρ σ1 e2 σ2 j

          {-@ π2 :: MapGE σ' σ2 @-}
          π2 :: Int -> Proof
          π2 j = trivial ? M.member j σ2 ? M.lookup' j σ'

  LEQLC e1 k w i -> if v1 == k
                    then proof
                       ? liquidAssert (vi == one)
                       ? liquidAssert (vw == zero)
                    else proof
                       ? liquidAssert (vi == zero)
                       ? liquidAssert (vw == 1/(v1-k))

    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
          proof = wgSoundE m ρ σ e1 σ1
                ? coherentEIncr m e1 σ1 σ' π
                ? π (outputWire e1)

          v1 = M.lookup' (outputWire e1) σ1
          vw = M.lookup' w σ'
          vi = M.lookup' i σ'

          {-@ π :: MapGE σ' σ1 @-}
          π :: Int -> Proof
          π j = liquidAssert (j /= i && j /= w) ? M.member j σ1 ? M.lookup' j σ'

  LNIL _ -> trivial
  LCONS e1 e2 -> wgSoundE m ρ σ e1 σ1        -- σ1 ⊢ e1 (by IH)
               ? coherentEIncr m e1 σ1 σ2 π1 -- σ2 ⊢ e1 (since σ2 ≥ σ1)
               ? coherentEIncr m e1 σ2 σ' π2 -- σ' ⊢ e1 (since σ' ≥ σ2)

               ? wgSoundE m ρ σ1 e2 σ2       -- σ2 ⊢ e2 (by IH)
               ? coherentEIncr m e2 σ2 σ' π2 -- σ' ⊢ e2 (since σ' ≥ σ2)

               ? π1 (outputWire e1) -- σ2[i1] == σ1[i1] (since σ2 ≥ σ1)
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s

          {-@ π1 :: MapGE σ2 σ1 @-}
          π1 :: Int -> Proof
          π1 j = wgIncr m ρ σ1 e2 σ2 j

          {-@ π2 :: MapGE σ' σ2 @-}
          π2 :: Int -> Proof
          π2 j = trivial ? M.member j σ2 ? M.lookup' j σ'
