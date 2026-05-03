{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.CompletenessVec where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import Utils
import TypeAliases

import Constraints
import DSL
import Label
import WitnessGeneration
import Semantics

import MapLemmas
import LabelingProof.RecursiveLemmas hiding (foo, barOp)
import LabelingProof.LabelingLemmas
import WitnessGenProof.WitnessGenLemmas
import WitnessGenProof.SemanticsLemmas

import Language.Haskell.Liquid.ProofCombinators

{-@ wgCompleteNil :: m0:Nat
                  -> τ:Ty -> e:{TypedDSL p | e = NIL τ}

                  -> ρ:NameValuation p
                  -> v:{DSLValue p | eval e ρ = Just v}
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> σ:WireValuation p m0

                  -> m:{Nat | m >= m0}
                  -> e':{LDSL p (Btwn 0 m) | wfE e' && freshE e' σ}
                  -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                          && sigmaVar m e' σ' = v } @-}
wgCompleteNil :: (Fractional p, Ord p)
              => Int -> Ty -> DSL p
              -> NameValuation p -> DSLValue p
              -> LabelEnv p Int -> WireValuation p
              -> Int -> LDSL p Int -> LabelEnv p Int
              -> WireValuation p
wgCompleteNil m0 τ e ρ v λ σ m e' λ' = σ


{-@ wgCompleteCons :: m0:Nat
                   -> e1:DSL p -> e2:DSL p
                   -> e:{TypedDSL p | e = CONS e1 e2}

                   -> ρ:NameValuation p
                   -> v1:{DSLValue p | eval e1 ρ = Just v1}
                   -> v2:{DSLValue p | eval e2 ρ = Just v2}
                   -> v:{DSLValue p | eval e ρ = Just v}
                   -> λ:LabelEnv p (Btwn 0 m0)
                   -> σ:WireValuation p m0

                   -> m1:{Nat | m1 >= m0}
                   -> e1':LDSL p (Btwn 0 m1)
                   -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

                   -> m2:{Nat | m2 >= m1}
                   -> e2':LDSL p (Btwn 0 m2)
                   -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                   -> m:{Nat | m >= m2}
                   -> e':{LDSL p (Btwn 0 m) | wfE e' && freshE e' σ}
                   -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                   -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1'
                                           && sigmaVar m e1' σ1 = v1}
                   -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 e2'
                                           && sigmaVar m e2' σ2 = v2}

                   -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                           && sigmaVar m e' σ' = v } @-}
wgCompleteCons :: (Fractional p, Ord p)
               => Int -> DSL p -> DSL p -> DSL p
               -> NameValuation p -> DSLValue p -> DSLValue p -> DSLValue p
               -> LabelEnv p Int -> WireValuation p

               -> Int -> LDSL p Int -> LabelEnv p Int
               -> Int -> LDSL p Int -> LabelEnv p Int
               -> Int -> LDSL p Int -> LabelEnv p Int

               -> WireValuation p -> WireValuation p -> WireValuation p
wgCompleteCons m0 e1 e2 e ρ v1 v2 v λ σ m1 e1' λ1 m2 e2' λ2 m e' λ' σ1 σ2 = σ2
  ? wgClosed  m ρ σ  e1' σ1            -- wires(e1') are bound in σ1
  ?? sigmaVarIncr m e1' σ1 σ2 σ2_gt_σ1 -- σ2(e1') = σ1(e1') since σ2 ≥ σ1

  where
    σ2_gt_σ1 = labelTyped e m0 λ m e' λ'   -- e' is well-typed
            ?? freshCons2 m ρ e1' e2' σ σ1 -- wires(e2') are free in σ1
            ?? wgIncr m ρ σ1 e2' σ2        -- σ2 ≥ σ1


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
