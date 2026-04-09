{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

module LabelingProof.LabelingBase where

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

import Language.Haskell.Liquid.ProofCombinators

{-@ agreeLemmaVar :: m0:Nat -> m:{Nat | m >= m0}
                  -> s:Var
                  -> τ:ScalarTy
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> σ:WireValuation p m0

                  -> Agree λ ρ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> e':{LDSL p (Btwn 0 m) | label' (VAR s τ) m0 λ = (m, e', λ')}
                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}

                  -> Agree λ' ρ σ' @-}
agreeLemmaVar :: (Fractional p, Eq p, Ord p)
              => Int -> Int -> Var -> Ty
              -> NameValuation p
              -> LabelEnv p Int
              -> WireValuation p

              -> (Var -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int
              -> WireValuation p

              -> (Var -> Proof)
agreeLemmaVar m0 m s τ ρ λ σ π λ' e' σ' = case M.lookup s λ of
  Just j -> π
  Nothing -> case τ of
    TF -> (\x -> if x == s
                 then trivial
                 else π x ? M.lookup' x λ)
    TBool -> (\x -> if x == s
                    then trivial
                    else π x ? M.lookup' x λ)


{-@ agreeLemmaConst :: m0:Nat -> m:{Nat | m >= m0}
                    -> k:p
                    -> ρ:NameValuation p
                    -> λ:LabelEnv p (Btwn 0 m0)
                    -> σ:WireValuation p m0

                    -> Agree λ ρ σ

                    -> λ':LabelEnv p (Btwn 0 m)
                    -> e':{LDSL p (Btwn 0 m) | label' (CONST k) m0 λ = (m, e', λ')}
                    -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}

                    -> Agree λ' ρ σ' @-}
agreeLemmaConst :: (Fractional p, Eq p, Ord p)
                => Int -> Int -> p
                -> NameValuation p
                -> LabelEnv p Int
                -> WireValuation p

                -> (Var -> Proof)

                -> LabelEnv p Int
                -> LDSL p Int
                -> WireValuation p

                -> (Var -> Proof)
agreeLemmaConst m0 m k ρ λ σ π λ' e' σ' x = π x ? notElemLemma x (outputWire e') λ


{-@ agreeLemmaBool :: m0:Nat -> m:{Nat | m >= m0}
                   -> b:Bool
                   -> ρ:NameValuation p
                   -> λ:LabelEnv p (Btwn 0 m0)
                   -> σ:WireValuation p m0

                   -> Agree λ ρ σ

                   -> λ':LabelEnv p (Btwn 0 m)
                   -> e':{LDSL p (Btwn 0 m) | label' (BOOL b) m0 λ = (m, e', λ')}
                   -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}

                   -> Agree λ' ρ σ' @-}
agreeLemmaBool :: (Fractional p, Eq p, Ord p)
               => Int -> Int -> Bool
               -> NameValuation p
               -> LabelEnv p Int
               -> WireValuation p

               -> (Var -> Proof)

               -> LabelEnv p Int
               -> LDSL p Int
               -> WireValuation p

               -> (Var -> Proof)
agreeLemmaBool m0 m b ρ λ σ π λ' e' σ' x = case b of
  True -> π x ? notElemLemma x (outputWire e') λ
  False -> π x ? notElemLemma x (outputWire e') λ
