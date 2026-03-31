{-# OPTIONS_GHC -Wno-redundant-constraints #-}
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

import MapLemmas
import Language.Haskell.Liquid.ProofCombinators

{-@ labelProofDIV :: m0:Nat -> m1:{Nat | m1 >= m0} -> m2:{Nat | m2 >= m1} -> m:{Nat | m >= m2}
                  -> p1:ScalarDSL p
                  -> p2:{ScalarDSL p | wellTyped (BIN DIV p1 p2)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> λ2:LabelEnv p (Btwn 0 m2)
                  -> σ:WireValuation p m0

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ  = (m1, p1', λ1)}
                  -> p2':{LDSL p (Btwn 0 m2) | label' p2 m1 λ1 = (m2, p2', λ2)}
                  -> e':{LDSL p (Btwn 0 m) | label' (BIN DIV p1 p2) m0 λ = (m, e', λ')}
                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ  e'}
                  -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ  p1'}
                  -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 p2'}

                  -> Agree λ2 ρ σ2

                  -> Agree λ' ρ σ' @-}
labelProofDIV :: (Fractional p, Ord p)
              => Int -> Int -> Int -> Int -> DSL p -> DSL p
              -> NameValuation p
              -> LabelEnv p Int -> LabelEnv p Int -> LabelEnv p Int
              -> WireValuation p

              -> LabelEnv p Int
              -> LDSL p Int -> LDSL p Int -> LDSL p Int
              -> WireValuation p -> WireValuation p -> WireValuation p

              -> (Var -> Proof)

              -> Var -> Proof
labelProofDIV m0 m1 m2 m p1 p2 ρ λ λ1 λ2 σ λ' p1' p2' e' σ' σ1 σ2 π2 x =
  π2 x ? notElemLemma x i λ2 ? notElemLemma x w λ2
  where (LDIV _ _ w i) = e'
