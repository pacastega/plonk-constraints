{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module WitnessGenProof.CompletenessOps where

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

{-@ wgCompleteUn :: m0:Nat
                 -> op:UnOp' p -> e1:DSL p
                 -> e:{TypedDSL p | e = UN op e1}

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

                 -> i:{Btwn 0 m | e' = LUN op e1' i}

                 -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1'
                                         && sigmaVar m e1' σ1 = VF v1}

                 -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                         && sigmaVar m e' σ' = VF v } @-}
wgCompleteUn :: (Fractional p, Ord p)
             => Int -> UnOp p -> DSL p -> DSL p
             -> NameValuation p -> p -> p
             -> LabelEnv p Int -> WireValuation p

             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int

             -> Int
             -> WireValuation p
             -> WireValuation p
wgCompleteUn m0 op e1 e ρ v1 v λ σ m1 e1' λ1 m e' λ' i σ1 =
  let σ' = M.insert i v σ1
  in labelType e m0 λ m e' λ' -- type(e') = type(e), so e' is also scalar
  ?? wfUn e1' op i       -- e1' is well-formed and well-typed

  ?? wgClosed  m ρ σ  e1' σ1         -- wires(e1') are bound in σ1

  ?? sigmaVarScalar m e1' σ1 -- sigmaVar(e1,σ1) = σ1[e1]
  ?? sigmaVarScalar m e'  σ' -- sigmaVar(e',σ') = σ'[e']

  ?? evalUnOp e1 op ρ v v1 -- valueUnOp op v1 = v

  ?? σ'

{-@ wgCompleteBin :: m0:Nat
                  -> op:BinOp' p -> e1:DSL p -> e2:DSL p
                  -> e:{TypedDSL p | e = BIN op e1 e2}

                  -> ρ:NameValuation p
                  -> v1:{p | eval e1 ρ = Just (VF v1)}
                  -> v2:{p | eval e2 ρ = Just (VF v2)}
                  -> v:{p | eval e ρ = Just (VF v)}
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

                  -> i:{Btwn 0 m | e' = LBIN op e1' e2' i}

                  -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1'
                                          && sigmaVar m e1' σ1 = VF v1}
                  -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 e2'
                                          && sigmaVar m e2' σ2 = VF v2}

                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                          && sigmaVar m e' σ' = VF v } @-}
wgCompleteBin :: (Fractional p, Ord p)
              => Int -> BinOp p -> DSL p -> DSL p -> DSL p
              -> NameValuation p -> p -> p -> p
              -> LabelEnv p Int -> WireValuation p

              -> Int -> LDSL p Int -> LabelEnv p Int
              -> Int -> LDSL p Int -> LabelEnv p Int
              -> Int -> LDSL p Int -> LabelEnv p Int

              -> Int
              -> WireValuation p
              -> WireValuation p
              -> WireValuation p
wgCompleteBin m0 op e1 e2 e ρ v1 v2 v λ σ m1 e1' λ1 m2 e2' λ2 m e' λ' i σ1 σ2 =
  let σ' = M.insert i v σ2
  in labelType e m0 λ m e' λ' -- type(e') = type(e), so e' is also scalar
  ?? wfBin e1' e2' op i       -- e1',e2' are well-formed and well-typed

  ?? wgClosed  m ρ σ  e1' σ1         -- wires(e1') are bound in σ1

  ?? freshBin2 m ρ e1' e2' op i σ σ1 -- wires(e2') are free  in σ1
  ?? wgKeysSet m ρ σ1 e2' σ2         -- keys(σ2) = keys(σ1) ∪ wires(e1')
  ?? wgClosed  m ρ σ1 e2' σ2         -- wires(e2') are bound in σ2

  ?? sigmaVarScalar m e1' σ1 -- sigmaVar(e1,σ1) = σ1[e1]
  ?? sigmaVarScalar m e2' σ2 -- sigmaVar(e2,σ2) = σ2[e2]
  ?? sigmaVarScalar m e'  σ' -- sigmaVar(e',σ') = σ'[e']

  ?? evalBinOp e1 e2 op ρ v v1 v2 -- valueBinOp op v1 v2 = v

  ?? σ'


{-@ typedScalarUn :: e1:DSL p
                  -> op:{UnOp p | wellTyped (UN op e1)}
                  -> { scalar (UN op e1) } @-}
typedScalarUn :: DSL p -> UnOp p -> Proof
typedScalarUn e1 op = case inferType (UN op e1) of Just _ -> trivial

{-@ typedScalarBin :: e1:DSL p -> e2:DSL p
                   -> op:{BinOp p | wellTyped (BIN op e1 e2)}
                   -> { scalar (BIN op e1 e2) } @-}
typedScalarBin :: DSL p -> DSL p -> BinOp p -> Proof
typedScalarBin e1 e2 op = case inferType (BIN op e1 e2) of Just _ -> trivial

-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
