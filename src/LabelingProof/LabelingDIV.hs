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
import WitnessGenProof.WitnessGenLemmas

import MapLemmas
import Language.Haskell.Liquid.ProofCombinators

-- if fresh(e1/e2, σ), then also fresh(e1,σ) and fresh(e2,σ1) ------------------
{-@ wgDivFresh1 :: m:Nat
                -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                -> w:Btwn 0 m -> i:Btwn 0 m
                -> σ:{WireValuation p m | freshE (LDIV e1 e2 w i) σ}
                -> { freshE e1 σ } @-}
wgDivFresh1 :: (Ord p, Fractional p) => Int
            -> LDSL p Int -> LDSL p Int -> Int -> Int
            -> WireValuation p
            -> Proof
wgDivFresh1 m e1 e2 w i σ = trivial

{-@ wgDivFresh2 :: m:Nat -> ρ:NameValuation p
                -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                -> w:Btwn 0 m -> i:{Btwn 0 m | wellTyped' (LDIV e1 e2 w i)
                                            && wfE (LDIV e1 e2 w i)}
                -> σ:{WireValuation p m | freshE (LDIV e1 e2 w i) σ}
                -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}
                -> { freshE e2 σ1 } @-}
wgDivFresh2 :: (Ord p, Fractional p) => Int -> NameValuation p
            -> LDSL p Int -> LDSL p Int -> Int -> Int
            -> WireValuation p -> WireValuation p
            -> Proof
wgDivFresh2 m ρ e1 e2 w i σ σ1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- if agree_Λ2(ρ,σ2) then also agree_Λ'(ρ,σ') ----------------------------------
{-@ agreeLemmaDIV :: m0:Nat -> m1:{Nat | m1 >= m0} -> m2:{Nat | m2 >= m1} -> m:{Nat | m >= m2}
                  -> p1:DSL p
                  -> p2:{DSL p | wellTyped (BIN DIV p1 p2)}
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
agreeLemmaDIV :: (Fractional p, Ord p)
              => Int -> Int -> Int -> Int -> DSL p -> DSL p
              -> NameValuation p
              -> LabelEnv p Int -> LabelEnv p Int -> LabelEnv p Int
              -> WireValuation p

              -> LabelEnv p Int
              -> LDSL p Int -> LDSL p Int -> LDSL p Int
              -> WireValuation p -> WireValuation p -> WireValuation p

              -> (Var -> Proof)

              -> Var -> Proof
agreeLemmaDIV m0 m1 m2 m p1 p2 ρ λ λ1 λ2 σ λ' p1' p2' e' σ' σ1 σ2 π2 x =
  π2 x ? notElemLemma x i λ2 ? notElemLemma x w λ2
  where (LDIV _ _ w i) = e'
