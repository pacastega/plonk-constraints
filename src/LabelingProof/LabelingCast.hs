{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--linear" @-}

module LabelingProof.LabelingCast where

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

import MapLemmas
import LabelingProof.LabelingLemmas
import WitnessGenProof.WitnessGenLemmas

import Language.Haskell.Liquid.ProofCombinators

-- if fresh(↑e1, σ), then also fresh(e1,σ) -------------------------------------
{-@ wgCastFresh1 :: m:Nat
                 -> e1:LDSL p (Btwn 0 m)
                 -> σ:{WireValuation p m | freshE (LBoolToF e1) σ}
                 -> { freshE e1 σ } @-}
wgCastFresh1 :: (Ord p, Fractional p)
             => Int -> LDSL p Int -> WireValuation p -> Proof
wgCastFresh1 m e1 σ = trivial


-- if agree_Λ1(ρ,σ1) then also agree_Λ'(ρ,σ') ----------------------------------
{-@ agreeLemmaCast :: m0:Nat -> m1:{Nat | m1 >= m0} -> m:{Nat | m >= m1}
                   -> p1:{DSL p | wellTyped (UN BoolToF p1)}
                   -> ρ:NameValuation p
                   -> λ:LabelEnv p (Btwn 0 m0)
                   -> λ1:LabelEnv p (Btwn 0 m1)
                   -> σ:WireValuation p m0

                   -> λ':LabelEnv p (Btwn 0 m)
                   -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ = (m1, p1', λ1)}
                   -> e':{LDSL p (Btwn 0 m) | label' (UN BoolToF p1) m0 λ = (m, e', λ')}
                   -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}
                   -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ p1'}

                   -> Agree λ1 ρ σ1

                   -> Agree λ' ρ σ' @-}
agreeLemmaCast :: (Fractional p, Eq p, Ord p)
               =>  Int -> Int -> Int -> DSL p
               -> NameValuation p
               -> LabelEnv p Int
               -> LabelEnv p Int
               -> WireValuation p

               -> LabelEnv p Int
               -> LDSL p Int
               -> LDSL p Int
               -> WireValuation p
               -> WireValuation p

               -> (Var -> Proof)

               -> Var -> Proof
agreeLemmaCast _m0 _m1 _m p1 ρ _λ λ1 _σ _λ' _p1' e' σ' σ1 π1 = π1
