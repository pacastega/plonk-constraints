{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.CompletenessEqlc where

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
import WitnessGenProof.CompletenessOps hiding (foo, barOp)
import WitnessGenProof.SemanticsLemmas

import Language.Haskell.Liquid.ProofCombinators


{-@ wgCompleteEqlc :: m0:Nat
                   -> e1:DSL p -> k:p
                   -> e:{TypedDSL p | e = UN (EQLC k) e1}

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

                   -> w:Btwn 0 m -> i:{Btwn 0 m | e' = LEQLC e1' k w i}

                   -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1'
                                           && sigmaVar m e1' σ1 = VF v1}

                   -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                           && sigmaVar m e' σ' = VF v } @-}
wgCompleteEqlc :: (Fractional p, Ord p)
               => Int -> DSL p -> p -> DSL p
               -> NameValuation p -> p -> p
               -> LabelEnv p Int -> WireValuation p

               -> Int -> LDSL p Int -> LabelEnv p Int
               -> Int -> LDSL p Int -> LabelEnv p Int

               -> Int -> Int
               -> WireValuation p -> WireValuation p
wgCompleteEqlc m0 e1 k e ρ v1 v λ σ m1 e1' λ1 m e' λ' w i σ1 =
  let wit = if v1 == k then zero else 1/(v1-k)
      σ' = M.insert i v (M.insert w wit σ1)
  in ()
  ?? labelType e m0 λ m e' λ' -- type(e') = type(e), so e' is also scalar
  ?? wfIsk e1' k w i          -- e1' is well-formed and well-typed

  ?? wgClosed m ρ σ e1' σ1 -- wires(e1') are bound in σ1

  ?? sigmaVarScalar m e1' σ1 -- sigmaVar(e1,σ1) = σ1[e1]
  ?? sigmaVarScalar m e'  σ' -- sigmaVar(e',σ') = σ'[e']

  ?? evalIsk e1 k ρ v v1 ?? liquidAssert (v == if v1 == k then one else zero)

  ?? σ'


{-@ evalIsk :: e1:DSL p -> k:{p | wellTyped (UN (EQLC k) e1)}
            -> ρ:NameValuation p
            -> v:{p | eval (UN (EQLC k) e1) ρ = Just (VF v)}
            -> v1:{p | eval e1 ρ = Just (VF v1)}
            -> { v = eqlFn k v1
                && v = if v1 == k then 1 else 0 } @-}
evalIsk :: (Fractional p, Eq p) => DSL p -> p -> NameValuation p
        -> p -> p -> Proof
evalIsk e1 k ρ v v1 = case eval (UN (EQLC k) e1) ρ of
  Just _ -> case eval e1 ρ of
    Just _ -> liquidAssert (v == eqlFn k v1)


-- explicit instantiation for ISZERO

{-@ wgCompleteIs0 :: m0:Nat
                  -> e1:DSL p
                  -> e:{TypedDSL p | e = UN ISZERO e1}

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

                  -> w:Btwn 0 m -> i:{Btwn 0 m | e' = LEQLC e1' 0 w i}

                  -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1'
                                          && sigmaVar m e1' σ1 = VF v1}

                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                          && sigmaVar m e' σ' = VF v } @-}
wgCompleteIs0 :: (Fractional p, Ord p)
              => Int -> DSL p -> DSL p
              -> NameValuation p -> p -> p
              -> LabelEnv p Int -> WireValuation p

              -> Int -> LDSL p Int -> LabelEnv p Int
              -> Int -> LDSL p Int -> LabelEnv p Int

              -> Int -> Int
              -> WireValuation p -> WireValuation p
wgCompleteIs0 m0 e1 _ ρ v1 v λ σ m1 e1' λ1 m e' λ' w i σ1 =
  wgCompleteEqlc m0 e1 0 (UN (EQLC 0) e1) ρ v1 v λ σ m1 e1' λ1 m e' λ' w i σ1


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
