{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.CompletenessEql where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import Utils
import TypeAliases

import Constraints
import DSL
import Label
import WitnessGeneration
import Semantics

import MapLemmas
import LabelingProof.RecursiveLemmas hiding (foo, barOp)
import LabelingProof.LabelingLemmas
import WitnessGenProof.WitnessGenLemmas
import WitnessGenProof.CompletenessOps hiding (foo, barOp)
import WitnessGenProof.CompletenessEqlc hiding (foo, barOp)
import WitnessGenProof.SemanticsLemmas

import Language.Haskell.Liquid.ProofCombinators


{-@ wgCompleteEql :: m0:Nat
                  -> e1:DSL p -> e2:DSL p
                  -> e:{TypedDSL p | e = BIN EQL e1 e2}

                  -> ρ:NameValuation p
                  -> v1:{p | eval e1 ρ = Just (VF v1)}
                  -> v2:{p | eval e2 ρ = Just (VF v2)}
                  -> v:{p | eval e ρ = Just (VF v)}
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> σ:WireValuation p m0

                  -> m1:{Nat | m1 >= m0}
                  -> e1':LDSL p (Btwn 0 m1)
                  -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

                  -> m2:{Nat | m2 >= m1}
                  -> e2':LDSL p (Btwn 0 m2)
                  -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                  -> m:{Nat | m >= m2}
                  -> e':{LDSL p (Btwn 0 m) | wfE e' && freshE e' σ}
                  -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                  -> d:Btwn 0 m -> w:Btwn 0 m
                  -> i:{Btwn 0 m | e' = LEQLC (LBIN SUB e1' e2' d) 0 w i}

                  -> σ1:{WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1'
                                          && evalWire m e1' σ1 = VF v1}
                  -> σ2:{WireValuation p m2 | Just σ2 = witnessGenE' m ρ σ1 e2'
                                          && evalWire m e2' σ2 = VF v2}

                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                          && evalWire m e' σ' = VF v } @-}
wgCompleteEql :: (Fractional p, Ord p)
              => Int -> DSL p -> DSL p -> DSL p
              -> NameValuation p -> p -> p -> p
              -> LabelEnv p Int -> WireValuation p

              -> Int -> LDSL p Int -> LabelEnv p Int
              -> Int -> LDSL p Int -> LabelEnv p Int
              -> Int -> LDSL p Int -> LabelEnv p Int

              -> Int -> Int -> Int
              -> WireValuation p -> WireValuation p -> WireValuation p
wgCompleteEql m0 e1 e2 e ρ v1 v2 v λ σ m1 e1' λ1 m2 e2' λ2 m e' λ' d w i σ1 σ2 =
  e'_eq ??
  sub_closed ??
  evalWireLemma m_sub m e'_sub σ_sub ??
  wt_e_alt ??
  evalBinOp e1 e2 SUB ρ v_sub v1 v2 ??
  evalEqlIs0Sub e1 e2 e (UN (EQLC 0) e_sub) ρ ??
  wgCompleteEqlc m0 e_sub 0 (UN (EQLC 0) e_sub)
                 ρ v_sub v λ σ
                 m_sub e'_sub λ_sub
                 m     e'     λ'
                 w i σ_sub
    where
      e_sub = BIN SUB e1 e2
      wt_sub = liquidAssert (wellTyped e_sub)
      wt_e_alt = liquidAssert (wellTyped (UN (EQLC 0) e_sub))
      e'_eq = liquidAssert (e' == LEQLC e'_sub 0 w i)
      (m_sub, e'_sub, λ_sub) = label' e_sub m0 λ
      m_sub_gt_m1_m2 = labelIncBin SUB e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m_sub e'_sub λ_sub
      m_ge_m_sub = labelEqlLemma e1 e2 m0 λ ?? wt_sub
                ?? labelIncUn (EQLC 0) e_sub m0 λ m_sub e'_sub λ_sub m e' λ'

      fresh_sub = m_ge_m_sub ?? freshIsk m e'_sub 0 w i σ

      wf_sub = labelTyped e m0 λ m e' λ' ?? wfIsk e'_sub 0 w i
      wf12 = wfBin e1' e2' SUB d

      fresh1 = fresh_sub ?? freshBin1 m e1' e2' SUB d σ
      σ1_lemma = m_ge_m_sub ?? fresh1 ?? wgLemma m_sub m ρ σ e1'
      evalWire1 = m_ge_m_sub ?? evalWireLemma m_sub m e1' σ1

      fresh2 = wf12 ?? fresh_sub ?? freshBin2 m ρ e1' e2' SUB d σ σ1
      σ2_lemma = m_ge_m_sub ?? fresh2 ?? wgLemma m_sub m ρ σ1 e2'
      evalWire2 = m_ge_m_sub ?? evalWireLemma m_sub m e2' σ2

      d = labelBin m0 e1 e2 λ SUB m1 e1' λ1 m2 e2' λ2 m_sub e'_sub λ_sub

      σ_sub = m_ge_m_sub ?? m_sub_gt_m1_m2
        ?? σ1_lemma ?? evalWire1
        ?? σ2_lemma ?? evalWire2

        ?? wf_sub
        ?? wgLemma m_sub m ρ σ e'_sub
        ?? evalBinOp e1 e2 SUB ρ v_sub v1 v2

        ?? wgCompleteBin m0 SUB e1 e2 e_sub ρ v1 v2 v_sub λ σ
                         m1 e1' λ1 m2 e2' λ2 m_sub e'_sub λ_sub d σ1 σ2

      sub_closed = wgClosed m_sub ρ σ e'_sub σ_sub
      Just (VF v_sub) = eval e_sub ρ


{-@ labelEqlLemma :: e1:DSL p -> e2:DSL p -> m0:Nat
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> { label' (BIN EQL e1 e2)               m0 λ =
                       label' (UN (EQLC 0) (BIN SUB e1 e2)) m0 λ } @-}
labelEqlLemma :: (Fractional p, Ord p) => DSL p -> DSL p -> Int
              -> LabelEnv p Int -> Proof
labelEqlLemma e1 e2 m0 λ = case label' (BIN EQL e1 e2) m0 λ of _ -> trivial


{-@ evalEqlIs0Sub :: e1:DSL p -> e2:DSL p
                  -> a:{TypedDSL p | a = BIN EQL e1 e2}
                  -> b:{TypedDSL p | b = UN (EQLC 0) (BIN SUB e1 e2)}
                  -> ρ:NameValuation p
                  -> { eval a ρ = eval b ρ } @-}
evalEqlIs0Sub :: (Fractional p, Eq p) => DSL p -> DSL p
              -> DSL p -> DSL p -> NameValuation p
              -> Proof
evalEqlIs0Sub e1 e2 a b ρ = case (eval e1 ρ, eval e2 ρ) of
  (Just (VF v1), Just (VF v2)) ->
    liquidAssert (eval a ρ == Just (VF (eqlFn v1 v2))) ?
    liquidAssert (eval b ρ == if v1-v2 == 0 then Just (VF 1) else Just (VF 0))
  _ -> trivial



{-@ evalEql :: e1:DSL p -> e2:{DSL p | wellTyped (BIN EQL e1 e2)}
            -> ρ:NameValuation p
            -> v:{p | eval (BIN EQL e1 e2) ρ = Just (VF v)}
            -> {v1:p | eval e1 ρ = Just (VF v1)}
            -> {v2:p | eval e2 ρ = Just (VF v2)}
            -> { v = eqlFn v1 v2 } @-}
evalEql :: (Fractional p, Eq p) => DSL p -> DSL p
        -> NameValuation p -> p -> p -> p -> Proof
evalEql e1 e2 ρ v v1 v2 = case eval (BIN EQL e1 e2) ρ of
  Just _ -> trivial



-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
