{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--linear" @-}

{-@ LIQUID "--fast" @-}
{-@ LIQUID "--eliminate=all" @-}

module LabelingProof.AgreeLemmaUn where

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

import WitnessGenProof.WitnessGenLemmas
import LabelingProof.LabelingLemmas
import MapLemmas

import Language.Haskell.Liquid.ProofCombinators

{-@ agreeLemmaUn :: m0:Nat -> m:{Nat | m >= m0}
               -> op:UnOp p -> e1:ScalarDSL p
               -> e:{ScalarDSL p | e = UN op e1}
               -> ρ:NameValuation p
               -> λ:LabelEnv p (Btwn 0 m0)
               -> σ:M.Map (Btwn 0 m0) p

               -> Agree λ ρ σ

               -> λ':LabelEnv p (Btwn 0 m)
               -> e':{LDSL p (Btwn 0 m) | wfE e' && freshE e' σ
                                       && label' e m0 λ = (m, mkList1 e', λ')}
               -> σ':{M.Map (Btwn 0 m) p | Just σ' = witnessGenE' m ρ σ e'}

               -> Agree λ' ρ σ'
               / [size e] @-}
agreeLemmaUn :: (Fractional p, Eq p, Ord p)
           => Int -> Int -> UnOp p -> DSL p -> DSL p
           -> NameValuation p
           -> LabelEnv p Int
           -> M.Map Int p

           -> (Var -> Proof)

           -> LabelEnv p Int
           -> LDSL p Int
           -> M.Map Int p

           -> (Var -> Proof)
agreeLemmaUn m0 m op e1 e ρ λ σ π λ' e' σ' = case op of
    ISZERO -> (\x -> π1 x ? M.lookup' x λ1)
      where (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
            π1 = agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1

    EQLC k -> (\x -> π1 x ? M.lookup' x λ1)
      where (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
            π1 = agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1

    BoolToF -> (\x -> π1 x ? M.lookup' x λ1)
      where (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
            π1 = agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1

    _ -> (\x -> π1 x ? M.lookup' x λ1)
      where (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
            π1 = agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1
