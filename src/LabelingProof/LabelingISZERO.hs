{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--linear" @-}
{-@ LIQUID "--eliminate=all" @-}

{-@ LIQUID "--cores=1" @-}

module LabelingProof.LabelingISZERO where

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


{-@ labelProofISZERO  :: m0:Nat -> m1:{Nat | m1 >= m0} -> m:{Nat | m >= m1}
                  -> p1:{ScalarDSL p | wellTyped (UN ISZERO p1)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> σ:M.Map (Btwn 0 m0) p

                  -> Composable ρ λ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ = (m1, mkList1 p1', λ1)}
                  -> e':{LDSL p (Btwn 0 m) | label' (UN ISZERO p1) m0 λ = (m, mkList1 e', λ')}
                  -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ e' σ}
                  -> σ1:{M.Map (Btwn 0 m1) p | Just σ1 = update m ρ p1' σ}

                  -> v:p -> v1:{p | M.lookup (outputWire p1') σ1 == Just v1}

                  -> ({ eval p1 ρ = Just (VF v1) <=> M.lookup (outputWire p1') σ1 = Just v1 })
                  -> Composable ρ λ1 σ1

                  -> ({ eval (UN ISZERO p1) ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v },
                    Composable ρ λ' σ') @-}
labelProofISZERO :: (Fractional p, Eq p, Ord p)
              => Int -> Int -> Int -> DSL p
              -> NameValuation p
              -> LabelEnv p Int
              -> LabelEnv p Int
              -> M.Map Int p

              -> (Var -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int
              -> LDSL p Int
              -> M.Map Int p
              -> M.Map Int p

              -> p -> p
              -> Proof -> (Var -> Proof)

              -> (Proof, Var -> Proof)
labelProofISZERO m0 m1 m p1 ρ λ λ1 σ π λ' p1' e' σ' σ1 v v1 ih1 π1
 = if v1 == 0
              then (ih1 ? (eval (UN ISZERO p1) ρ === fmap' (eqlFn (VF 0)) (eval p1 ρ) === Just (eqlFn (VF 0) (VF v1))),
                   \x -> let j = M.lookup' x λ1
                         in π1 x ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                                 ? (M.lookup j σ'
                                    === M.lookup j (M.insert w zero σ1)
                                    === M.lookup j σ1))
                   ? liquidAssert (σ' == M.insert i one (M.insert w zero σ1))
              else (ih1 ? (eval (UN ISZERO p1) ρ === fmap' (eqlFn (VF 0)) (eval p1 ρ) === Just (eqlFn (VF 0) (VF v1))),
                   \x -> let j = M.lookup' x λ1
                         in π1 x ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                                 ? (M.lookup j σ'
                                    === M.lookup j (M.insert w (1/v1) σ1)
                                    === M.lookup j σ1))
                   ? liquidAssert (σ' == M.insert i zero (M.insert w (1/v1) σ1))
      where (LEQLC _ _ w i) = e'
            (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case update m1 ρ p1' σ ? updateLemma m1 m ρ p1' σ of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
