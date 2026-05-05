{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.CompletenessDiv where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

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


{-@ wgCompleteDiv :: m0:Nat
                  -> e1:DSL p -> e2:DSL p
                  -> e:{TypedDSL p | e = BIN DIV e1 e2}

                  -> ρ:NameValuation p
                  -> v1:{p | eval e1 ρ = Just (VF v1)}
                  -> v2:{p | eval e2 ρ = Just (VF v2) && v2 /= 0}
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

                  -> w:Btwn 0 m -> i:{Btwn 0 m | e' = LDIV e1' e2' w i}

                  -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1'
                                          && sigmaVar m e1' σ1 = VF v1}
                  -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 e2'
                                          && sigmaVar m e2' σ2 = VF v2}

                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                          && sigmaVar m e' σ' = VF v } @-}
wgCompleteDiv :: (Fractional p, Ord p)
              => Int -> DSL p -> DSL p -> DSL p
              -> NameValuation p -> p -> p -> p
              -> LabelEnv p Int -> WireValuation p

              -> Int -> LDSL p Int -> LabelEnv p Int
              -> Int -> LDSL p Int -> LabelEnv p Int
              -> Int -> LDSL p Int -> LabelEnv p Int

              -> Int -> Int
              -> WireValuation p -> WireValuation p -> WireValuation p
wgCompleteDiv m0 e1 e2 e ρ v1 v2 v λ σ m1 e1' λ1 m2 e2' λ2 m e' λ' w i σ1 σ2 =
  let σ' = M.insert w (1/v2) (M.insert i v σ2)
  in ()

  ?? labelType e m0 λ m e' λ'  -- type(e') = type(e), so e' is also scalar
  ?? wfDiv e1' e2' w i         -- e1',e2' are well-formed and well-typed

  ?? wgClosed  m ρ σ  e1' σ1         -- wires(e1') are bound in σ1

  ?? freshDiv2 m ρ e1' e2' w i σ σ1 -- wires(e2') are free  in σ1
  ?? wgKeysSet m ρ σ1 e2' σ2        -- keys(σ2) = keys(σ1) ∪ wires(e1')
  ?? wgClosed  m ρ σ1 e2' σ2        -- wires(e2') are bound in σ2

  ?? sigmaVarScalar m e1' σ1 -- sigmaVar(e1,σ1) = σ1[e1]
  ?? sigmaVarScalar m e2' σ2 -- sigmaVar(e2,σ2) = σ2[e2]
  ?? sigmaVarScalar m e'  σ' -- sigmaVar(e',σ') = σ'[e']

  ?? evalDiv e1 e2 ρ v v1 v2
  ?? σ'


{-@ evalDiv :: e1:DSL p -> e2:{DSL p | wellTyped (BIN DIV e1 e2)}
            -> ρ:NameValuation p
            -> v:{p | eval (BIN DIV e1 e2) ρ = Just (VF v)}
            -> {v1:p | eval e1 ρ = Just (VF v1)}
            -> {v2:p | eval e2 ρ = Just (VF v2) && v2 /= 0}
            -> { v = v1 / v2 } @-}
evalDiv :: (Fractional p, Eq p) => DSL p -> DSL p
        -> NameValuation p -> p -> p -> p -> Proof
evalDiv e1 e2 ρ v v1 v2 = case eval (BIN DIV e1 e2) ρ of
  Just _ -> case (eval e1 ρ, eval e2 ρ) of
    (Just (VF _), Just (VF _)) -> liquidAssert (v == v1 / v2)


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
