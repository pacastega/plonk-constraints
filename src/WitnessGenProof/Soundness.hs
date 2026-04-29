{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
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

import LabelingProof.RecursiveLemmas

import LabelingProof.LabelingCast
import LabelingProof.LabelingDIV
import LabelingProof.LabelingEQLC
import LabelingProof.LabelingEQL
import LabelingProof.LabelingISZERO
import LabelingProof.LabelingOps
import LabelingProof.LabelingVec

import Language.Haskell.Liquid.ProofCombinators


{-@ wgSoundE :: m:Nat
             -> ρ:NameValuation p
             -> σ:WireValuation p m
             -> {e:TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ}
             -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
             -> { coherentE m e σ' } @-}
wgSoundE :: (Ord p, Fractional p)
         => Int -> NameValuation p -> WireValuation p -> LDSL p Int
         -> WireValuation p -> Proof
wgSoundE m ρ σ e σ' = case e of
  LWIRE τ i -> wgSoundWire m ρ σ τ i σ'
  LVAR s τ i -> wgSoundVar m ρ σ s τ i σ'
  LCONST x i -> wgSoundConst m ρ σ x i σ'
  LBOOL b i -> wgSoundBool m ρ σ b i σ'

  LDIV e1 e2 w i -> wf12 -- e1,e2 are well-formed and well-typed

                  ? fresh1               -- wires(e1) are free  in σ
                  ? wgClosed m ρ σ e1 σ1 -- wires(e1) are bound in σ1
                  ? wgSoundE m ρ σ e1 σ1 -- σ1 ⊢ e1 (IH 1)

                  ? coherentEIncr m e1 σ1 σ2 π1 -- σ2 ⊢ e1 (since σ2 ≥ σ1)
                  ? wgKeysSet m ρ σ1 e2 σ2      -- keys(σ2) = keys(σ1) ∪ wires(e2)
                  ? coherentEIncr m e1 σ2 σ' π2 -- σ' ⊢ e1 (since σ' ≥ σ2)

                  ? fresh2                -- wires(e2) are free  in σ1
                  ? wgClosed m ρ σ1 e2 σ2 -- wires(e2) are bound in σ2
                  ? wgSoundE m ρ σ1 e2 σ2 -- σ2 ⊢ e2 (IH 2)

                  ? coherentEIncr m e2 σ2 σ' π2 -- σ' ⊢ e2 (since σ' ≥ σ2)

                  ? π1 i1 ? π2 i1 -- σ'[i1] = σ1[i1] = v1 (since σ' ≥ σ2 ≥ σ1)
                  ? π2 i2         -- σ'[i2] = σ2[i2] = v2 (since σ' ≥ σ2)

                  ? wgLemmaDiv m e1 e2 w i e ρ σ σ' σ1 σ2 v1 v2 -- v2 /= 0
                                                                -- σ'[i] = v1 / v2
                                                                -- σ'[w] = 1/v2

                  ? liquidAssert (v2 /= 0)
                  ? liquidAssert (vw == 1 / v2)
                  ? liquidAssert (vw * v2 == 1)
                  ? liquidAssert (vi == v1 / v2)

                  ? wgClosed m ρ σ e σ'
                  ? liquidAssert (coherentE m e σ')

    where σ1 = σ1Div m m ρ σ e1 e2 w i e σ'
          σ2 = σ2Div m m ρ σ e1 e2 w i e σ' σ1

          i1 = scalar12 ?? outputWire e1 ?          wgOutputMem m ρ σ  e1 σ1
          i2 = scalar12 ?? outputWire e2 ? fresh2 ? wgOutputMem m ρ σ1 e2 σ2

          v1 = M.lookup' i1 σ1
          v2 = M.lookup' i2 σ2
          vw = wgOutputMemDiv m ρ σ e1 e2 w i e σ' ?? M.lookup' w σ'
          vi = wgOutputMemDiv m ρ σ e1 e2 w i e σ' ?? M.lookup' i σ'

          fresh1 = freshDiv1 m   e1 e2 w i σ    -- wires(e1) are free in σ
          fresh2 = freshDiv2 m ρ e1 e2 w i σ σ1 -- wires(e2) are free in σ1
          wf12 = wfDiv e1 e2 w i             -- e1,e2 are well-formed and well-typed
          scalar12 = scalarDiv m e1 e2 w i -- e1,e2 are scalars

          {-@ π1 :: MapGE σ2 σ1 @-} -- σ2 ≥ σ1
          π1 j = fresh2 ?? wf12 ?? wgIncr m ρ σ1 e2 σ2 j

          {-@ π2 :: MapGE σ' σ2 @-} -- σ' ≥ σ2
          π2 = wgIncrDiv m e1 e2 w i e ρ σ σ' σ1 σ2

  LUN op e1 i -> case op of
    ADDC k -> proof; MULC k -> proof; UnsafeNOT -> proof;
    NOT -> proof;
    where σ1 = σ1Un m m ρ σ e1 op i e σ'
          proof = wf1 -- e1 is well-formed and well-typed

                ? fresh1               -- wires(e1) are free  in σ
                ? wgClosed m ρ σ e1 σ1 -- wires(e1) are bound in σ1
                ? wgSoundE m ρ σ e1 σ1 -- σ1 ⊢ e1 (IH)

                ? coherentEIncr m e1 σ1 σ' π1 -- σ' ⊢ e1 (since σ' ≥ σ1)

                ? π1 i1 -- σ'[i1] = σ1[i1] = v1 (since σ' ≥ σ1)
                ? wgLemmaUn m e1 op i e ρ σ σ' σ1 v1 -- σ'[i] = □v1

                ? wgClosed m ρ σ e σ'
                ? liquidAssert (coherentE m e σ')

          i1 = scalarUn m e1 op i ?? outputWire e1
          v1 = fresh1 ?? wgOutputMem m ρ σ e1 σ1 ?? M.lookup' i1 σ1

          wf1 = wfUn e1 op i -- e1 is well-formed and well-typed
          fresh1 = freshUn m e1 op i σ -- wires(e1) are free in σ

          {-@ π1 :: MapGE σ' σ1 @-}
          π1 = wgIncrUn m e1 op i e ρ σ σ' σ1


  LBIN op e1 e2 i -> case op of
    ADD -> proof; SUB -> proof; MUL -> proof; LINCOMB _ _ -> proof;
    AND -> proof; OR  -> proof; XOR -> proof;
    UnsafeAND -> proof; UnsafeOR  -> proof; UnsafeXOR -> proof;
    where σ1 = σ1Bin m m ρ σ e1 e2 op i e σ'
          σ2 = σ2Bin m m ρ σ e1 e2 op i e σ' σ1
          proof = wf12 -- e1,e2 are well-formed and well-typed

                ? fresh1                -- wires(e1) are free  in σ
                ? wgClosed m ρ σ e1 σ1  -- wires(e1) are bound in σ1
                ? wgSoundE m ρ σ e1 σ1  -- σ1 ⊢ e1 (IH 1)

                ? coherentEIncr m e1 σ1 σ2 π1 -- σ2 ⊢ e1 (since σ2 ≥ σ1)
                ? wgKeysSet m ρ σ1 e2 σ2      -- keys(σ2) = keys(σ1) ∪ wires(e2)
                ? coherentEIncr m e1 σ2 σ' π2 -- σ' ⊢ e1 (since σ' ≥ σ2)

                ? fresh2                -- wires(e2) are free  in σ1
                ? wgClosed m ρ σ1 e2 σ2 -- wires(e2) are bound in σ2
                ? wgSoundE m ρ σ1 e2 σ2 -- σ2 ⊢ e2 (IH 2)

                ? coherentEIncr m e2 σ2 σ' π2 -- σ' ⊢ e2 (since σ' ≥ σ2)

                ? π1 i1 ? π2 i1 -- σ'[i1] = σ1[i1] = v1 (since σ' ≥ σ2 ≥ σ1)
                ? π2 i2         -- σ'[i2] = σ2[i2] = v2 (since σ' ≥ σ2)
                ? wgLemmaBin m e1 e2 op i e ρ σ σ' σ1 σ2 v1 v2 -- σ'[i] = v1⮾v2

                ? wgClosed m ρ σ e σ' -- wires(e) are bound in σ'
                ? liquidAssert (coherentE m e σ')

          i1 = scalar12 ?? outputWire e1
          i2 = scalar12 ?? outputWire e2
          v1 =           wgOutputMem m ρ σ  e1 σ1 ?? M.lookup' i1 σ1
          v2 = fresh2 ?? wgOutputMem m ρ σ1 e2 σ2 ?? M.lookup' i2 σ2

          fresh1 = freshBin1 m   e1 e2 op i σ    -- wires(e1) are free in σ
          fresh2 = freshBin2 m ρ e1 e2 op i σ σ1 -- wires(e2) are free in σ1
          wf12 = wfBin e1 e2 op i             -- e1,e2 are well-formed and well-typed
          scalar12 = scalarBin m e1 e2 op i -- e1,e2 are scalars

          {-@ π1 :: MapGE σ2 σ1 @-} -- σ2 ≥ σ1
          π1 j = fresh2 ?? wf12 ?? wgIncr m ρ σ1 e2 σ2 j

          {-@ π2 :: MapGE σ' σ2 @-} -- σ' ≥ σ2
          π2 = wgIncrBin m e1 e2 op i e ρ σ σ' σ1 σ2

  LBoolToF e1 -> proof
    where σ1 = σ1Cast m m ρ σ e1 e σ'
          proof = wf1

                ? freshCast m e1 σ
                ? wgClosed m ρ σ e1 σ1
                ? wgSoundE m ρ σ e1 σ1

                ? coherentEIncr m e1 σ1 σ' π1

                ? wgClosed m ρ σ e σ'
                ? liquidAssert (coherentE m e σ')

          wf1 = wfCast e1

          {-@ π1 :: MapGE σ' σ1 @-}
          π1 :: Int -> Proof
          π1 j = liquidAssert (σ' == σ1)

  LEQLC e1 k w i -> if v1 == k
                    then proof
                       ? liquidAssert (valueIsk_i k v1 == one)
                       ? liquidAssert (valueIsk_w k v1 == zero)
                       ? boolean one
                       ? (coherentE m e σ')
                    else proof
                       ? liquidAssert (valueIsk_i k v1 == zero)
                       ? liquidAssert (valueIsk_w k v1 == 1/(v1-k))
                       ? boolean zero
                       ? liquidAssert (coherentE m e σ')

    where σ1 = σ1Isk m m ρ σ e1 k w i e σ'
          proof = wf1 -- e1 is well-formed and well-type

                ? fresh1               -- wires(e1) are free  in σ
                ? wgClosed m ρ σ e1 σ1 -- wires(e1) are bound in σ1
                ? wgSoundE m ρ σ e1 σ1 -- σ1 ⊢ e1 (IH)

                ? coherentEIncr m e1 σ1 σ' π1 -- σ' ⊢ e1 (since σ' ≥ σ1)

                ? π1 i1 -- σ'[i1] = σ1[i1] = v1 (since σ' ≥ σ1)

                ? wgLemmaIsk m e1 k w i e ρ σ σ' σ1 v1
                ? wgClosed m ρ σ e σ'

          i1 = scalarIsk m e1 k w i ?? outputWire e1
          v1 = fresh1 ?? wgOutputMem m ρ σ e1 σ1 ?? M.lookup' i1 σ1

          wf1 = wfIsk e1 k w i
          fresh1 = freshIsk m e1 k w i σ

          {-@ π1 :: MapGE σ' σ1 @-}
          π1 = wgIncrIsk m e1 k w i e ρ σ σ' σ1

  LNIL _ -> wgClosed m ρ σ e σ'
          ? liquidAssert (coherentE m e σ')
  LCONS e1 e2 -> wf12 -- e1,e2 are well-formed and well-typed

               ? fresh1               -- wires(e1) are free  in σ
               ? wgClosed m ρ σ e1 σ1 -- wires(e1) are bound in σ1
               ? wgSoundE m ρ σ e1 σ1 -- σ1 ⊢ e1 (IH 1)

               ? coherentEIncr m e1 σ1 σ2 π1 -- σ2 ⊢ e1 (since σ2 ≥ σ1)
               ? wgKeysSet m ρ σ1 e2 σ2      -- keys(σ2) = keys(σ1) ∪ wires(e2)
               ? coherentEIncr m e1 σ2 σ' π2 -- σ' ⊢ e1 (since σ' ≥ σ2)

               ? fresh2                -- wires(e2) are free  in σ1
               ? wgClosed m ρ σ1 e2 σ2 -- wires(e2) are bound in σ2
               ? wgSoundE m ρ σ1 e2 σ2 -- σ2 ⊢ e2 (IH 2)

               ? coherentEIncr m e2 σ2 σ' π2 -- σ' ⊢ e2 (since σ' ≥ σ2)

               ? wgClosed m ρ σ e σ'
               ? liquidAssert (coherentE m e σ')

    where σ1 = σ1Cons m m ρ σ e1 e2 e σ'
          σ2 = σ2Cons m m ρ σ e1 e2 e σ' σ1

          wf12 = wfCons e1 e2
          fresh1 = freshCons1 m e1 e2 σ
          fresh2 = freshCons2 m ρ e1 e2 σ σ1

          {-@ π1 :: MapGE σ2 σ1 @-} -- σ2 ≥ σ1
          π1 j = wf12 ?? wgIncr m ρ σ1 e2 σ2 j

          {-@ π2 :: MapGE σ' σ2 @-} -- σ' ≥ σ2
          π2 :: Int -> Proof
          π2 = wgIncrCons m e1 e2 e ρ σ σ' σ1 σ2
