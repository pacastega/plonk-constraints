{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--linear" @-}
{-@ LIQUID "--fast" @-}

module LabelingProof.AgreeLemma where

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

import Language.Haskell.Liquid.ProofCombinators

{-@ agreeLemma :: m0:Nat -> m:{Nat | m >= m0}
               -> e:ScalarDSL p
               -> ρ:NameValuation p
               -> λ:LabelEnv p (Btwn 0 m0)
               -> σ:M.Map (Btwn 0 m0) p

               -> Agree λ ρ σ

               -> λ':LabelEnv p (Btwn 0 m)
               -> e':{LDSL p (Btwn 0 m) | label' e m0 λ = (m, mkList1 e', λ')}
               -> σ':{M.Map (Btwn 0 m) p | Just σ' = witnessGenE' m ρ σ e'}

               -> Agree λ' ρ σ'
               / [size e] @-}
agreeLemma :: (Fractional p, Eq p, Ord p)
           => Int -> Int -> DSL p
           -> NameValuation p
           -> LabelEnv p Int
           -> M.Map Int p

           -> (Var -> Proof)

           -> LabelEnv p Int
           -> LDSL p Int
           -> M.Map Int p

           -> (Var -> Proof)
agreeLemma m0 m e ρ λ σ π λ' e' σ' = case e of
  VAR s τ -> labelVar m0 m s τ ρ λ σ π λ' e' σ' v
  CONST _ -> (\x -> π x ? notElemLemma' x (outputWire e') λ)

  BOOL b -> case b of
    True -> (\x -> π x ? notElemLemma' x (outputWire e') λ)
    False -> (\x -> π x ? notElemLemma' x (outputWire e') λ)

  UN  op p1 -> case op of

    ISZERO -> label1Inc op p1 m0 λ m1 p1' λ1 m e' λ'
      ?? labelProofISZERO m0 m1 m p1 ρ λ λ1 σ π λ' p1' e' σ' σ1 v v1 ih1 π1
      where (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1

    EQLC k -> label1Inc op p1 m0 λ m1 p1' λ1 m e' λ'
      ?? labelProofEQLC m0 m1 m k p1 ρ λ λ1 σ π λ' p1' e' σ' σ1 v v1 ih1 π1
      where (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
    BoolToF -> case M.lookup (outputWire p1') σ1 of
        Just v1 -> agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
        Nothing -> case eval p1 ρ of
          Just (VF v1') -> agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1'
          Nothing -> agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 0
      where (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s

    _ -> label1Inc op p1 m0 λ m1 p1' λ1 m e' λ'
      ?? labelProofUn  m0 m1 m p1 op ρ λ λ1 σ π λ' p1' e' σ' σ1 v v1 ih1 π1
      where (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = agreeLemma m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1


  BIN op p1 p2 -> case op of

    DIV -> label2Inc DIV p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ'
      ?? labelProofDIV m0 m1 m2 m p1 p2 ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 v v1 v2 ih1 π1 ih2 π2
      where (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
            σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2

    EQL -> label2Inc EQL p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ'
      ?? labelProofEQL m0 m1 m2 m p1 p2 ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 v v1 v2 ih1 π1 ih2 π2
      where (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
            σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
    _ -> label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ'
      ?? labelProofBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 v v1 v2 ih1 π1 ih2 π2
      where (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
            σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2


{-@ assume admit :: () -> { False } @-}
admit :: () -> ()
admit _ = ()
