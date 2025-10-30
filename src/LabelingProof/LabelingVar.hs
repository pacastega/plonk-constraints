{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

{-@ LIQUID "--cores=1" @-}

module LabelingProof.LabelingVar where

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

import Language.Haskell.Liquid.ProofCombinators


{-@ labelVar :: m0:Nat -> m:{Nat | m >= m0}
                -> s:Var
                -> τ:ScalarTy
                -> ρ:NameValuation p
                -> λ:LabelEnv p (Btwn 0 m0)
                -> σ:M.Map (Btwn 0 m0) p

                -> Composable ρ λ σ

                -> λ':LabelEnv p (Btwn 0 m)
                -> e':{LDSL p (Btwn 0 m) | label' (VAR s τ) m0 λ = (m, mkList1 e', λ')}
                -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ e' σ}

                -> v:p

                -> ({ eval (VAR s τ) ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v },
                    Composable ρ λ' σ')
                 @-}
labelVar :: (Fractional p, Eq p, Ord p)
            => Int -> Int -> Var -> Ty
            -> NameValuation p
            -> LabelEnv p Int
            -> M.Map Int p

            -> (Var -> Proof)

            -> LabelEnv p Int
            -> LDSL p Int
            -> M.Map Int p

            -> p

            -> (Proof, Var -> Proof)
labelVar _m0 _m s τ _ρ λ _σ π λ' e' _σ' _v = case M.lookup s λ of
    Nothing -> case τ of
      TF -> (trivial,
             \x -> if x == s
                   then trivial
                   else elem' x (M.keys λ')
                     ?? freshLemma (outputWire e') λ ? π x ? M.lookup' x λ)
      TBool -> (trivial,
               \x -> if x == s
                     then trivial
                     else elem' x (M.keys λ')
                       ?? freshLemma (outputWire e') λ ? π x ? M.lookup' x λ)
    Just j  -> (elementLemma s j λ ? π s ? lookupLemma s λ, \x -> π x)
