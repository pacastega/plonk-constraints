{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.CompletenessCast where

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

{-@ wgCompleteCast :: m0:Nat -> e1:DSL p
                   -> e:{TypedDSL p | e = UN BoolToF e1}

                   -> ρ:NameValuation p
                   -> v1:{p | eval e1 ρ = Just (VF v1)}
                   -> v:{p | eval e ρ = Just (VF v)}
                   -> λ:LabelEnv p (Btwn 0 m0)
                   -> σ:WireValuation p m0

                   -> m1:{Nat | m1 >= m0}
                   -> e1':LDSL p (Btwn 0 m1)
                   -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

                   -> m:{Nat | m >= m1}
                   -> e':{LDSL p (Btwn 0 m) | wfE e' && freshE e' σ}
                   -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                   -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1'
                                           && sigmaVar m e1' σ1 = VF v1}

                   -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                           && sigmaVar m e' σ' = VF v } @-}
wgCompleteCast :: (Fractional p, Ord p)
               => Int -> DSL p -> DSL p
               -> NameValuation p -> p -> p
               -> LabelEnv p Int -> WireValuation p

               -> Int -> LDSL p Int -> LabelEnv p Int
               -> Int -> LDSL p Int -> LabelEnv p Int

               -> WireValuation p
               -> WireValuation p
wgCompleteCast m0 e1 e ρ v1 v λ σ m1 e1' λ1 m e' λ' σ1 = σ1
   ? labelTyped e m0 λ m e' λ' -- type(e') = type(e), so e' is also well-typed
  ?? wgClosed  m ρ σ  e1' σ1   -- wires(e1') are bound in σ1
  ?? sigmaVarScalar m e1' σ1   -- sigmaVar(e1,σ1) = σ1[e1]


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
