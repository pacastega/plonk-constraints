{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--ple"           @-}
{-@ LIQUID "--eliminate=all" @-}
{-@ LIQUID "--linear"        @-}
{-@ LIQUID "--cores=1"       @-}

module LabelingProof.LabelingDIV where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import Utils
import TypeAliases

import Vec
import DSL
import Label
import WitnessGeneration
import Semantics

import LabelingProof.LabelingLemmas

import Language.Haskell.Liquid.ProofCombinators

{-@ labelProofDIV :: m0:Nat -> m1:{Nat | m1 >= m0} -> m2:{Nat | m2 >= m1} -> m:{Nat | m >= m2}
                  -> p1:ScalarDSL p
                  -> p2:{ScalarDSL p | wellTyped (BIN DIV p1 p2)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> λ2:LabelEnv p (Btwn 0 m2)
                  -> σ:M.Map (Btwn 0 m0) p

                  -> Composable ρ λ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ  = (m1, mkList1 p1', λ1)}
                  -> p2':{LDSL p (Btwn 0 m2) | label' p2 m1 λ1 = (m2, mkList1 p2', λ2)}
                  -> e':{LDSL p (Btwn 0 m) | label' (BIN DIV p1 p2) m0 λ = (m, mkList1 e', λ')}
                  -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ e' σ}
                  -> σ1:{M.Map (Btwn 0 m1) p | Just σ1 = update m ρ p1' σ}
                  -> σ2:{M.Map (Btwn 0 m2) p | Just σ2 = update m ρ p2' σ1}


                  -> v:p
                  -> v1:{p | M.lookup (outputWire p1') σ1 == Just v1}
                  -> v2:{p | M.lookup (outputWire p2') σ2 == Just v2}

                  -> ({ eval p1 ρ = Just (VF v1) <=> M.lookup (outputWire p1') σ1 = Just v1 })
                  -> Composable ρ λ1 σ1

                  -> ({ eval p2 ρ = Just (VF v2) <=> M.lookup (outputWire p2') σ2 = Just v2 })
                  -> Composable ρ λ2 σ2



                  -> ({ eval (BIN DIV p1 p2) ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v }, Composable ρ λ' σ')
 @-}
labelProofDIV :: (Fractional p, Ord p)
              => Int -> Int -> Int -> Int -> DSL p -> DSL p
              -> NameValuation p
              -> LabelEnv p Int -> LabelEnv p Int -> LabelEnv p Int
              -> M.Map Int p

              -> (Var -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int -> LDSL p Int -> LDSL p Int
              -> M.Map Int p -> M.Map Int p -> M.Map Int p

              -> p -> p -> p

              -> Proof -> (Var -> Proof)
              -> Proof -> (Var -> Proof)

              -> (Proof, Var -> Proof)
labelProofDIV _m0 _m1 _m2 _m _p1 _p2 _ρ _λ _λ1 λ2 _σ _π _λ' _p1' _p2' e' σ' _σ1 σ2 _v v1 v2 ih1 _π1 ih2 π2
  = (ih1 ? ih2,
           \x -> let j = M.lookup' x λ2
                 in π2 x ? notElemLemma' x i λ2 ? notElemLemma' x w λ2
                         ? (M.lookup j σ'
                            === M.lookup j (M.insert i (v1/v2) σ2)
                            === M.lookup j σ2))
      where (LDIV _ _ w i) = e'
