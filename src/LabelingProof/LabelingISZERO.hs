{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--linear" @-}
{-@ LIQUID "--fast" @-}

module LabelingProof.LabelingISZERO where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import Utils
import TypeAliases

import Vec
import DSL
import Label
import WitnessGeneration
import Semantics

import LabelingProof.LabelingLemmas
import WitnessGenProof.WitnessGenLemmas

import MapLemmas
import Language.Haskell.Liquid.ProofCombinators


{-@ agreeLemmaISZERO :: m0:Nat -> m1:{Nat | m1 >= m0} -> m:{Nat | m >= m1}
                  -> p1:{ScalarDSL p | wellTyped (UN ISZERO p1)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> σ:WireValuation p m0

                  -> Agree λ ρ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | wfE p1'
                                        && freshE p1' σ
                                        && label' p1 m0 λ = (m1, p1', λ1)}
                  -> e':{LDSL p (Btwn 0 m) | wfE e'
                                        && freshE e' σ
                                        && label' (UN ISZERO p1) m0 λ = (m, e', λ')}
                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}
                  -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ p1'}

                  -> Agree λ1 ρ σ1

                  -> Agree λ' ρ σ' @-}
agreeLemmaISZERO :: (Fractional p, Eq p, Ord p)
              => Int -> Int -> Int -> DSL p
              -> NameValuation p
              -> LabelEnv p Int
              -> LabelEnv p Int
              -> WireValuation p

              -> (Var -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int
              -> LDSL p Int
              -> WireValuation p
              -> WireValuation p

              -> (Var -> Proof)

              -> (Var -> Proof)
agreeLemmaISZERO m0 m1 m p1 ρ λ λ1 σ π λ' p1' e' σ' σ1 π1 x =
  π1 x ? notElemLemma x i λ1 ? notElemLemma x w λ1
  where (LEQLC _ _ w i) = e'
