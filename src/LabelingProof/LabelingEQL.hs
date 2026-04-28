{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--ple"           @-}
{-@ LIQUID "--linear"        @-}

module LabelingProof.LabelingEQL where

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
import LabelingProof.LabelingEQLC
import WitnessGenProof.WitnessGenLemmas

import Language.Haskell.Liquid.ProofCombinators


-- if fresh(e1==e2, σ), then also fresh(e1,σ) and fresh(e2,σ1) -----------------
{-@ wgEqlFresh1 :: m:Nat
                -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                -> d:Btwn 0 m -> w:Btwn 0 m -> i:Btwn 0 m
                -> σ:{WireValuation p m | freshE (LEQLC (LBIN SUB e1 e2 d) 0 w i) σ}
                -> { freshE e1 σ } @-}
wgEqlFresh1 :: (Ord p, Fractional p) => Int
            -> LDSL p Int -> LDSL p Int -> Int -> Int -> Int
            -> WireValuation p
            -> Proof
wgEqlFresh1 m e1 e2 d w i σ = trivial

{-@ wgEqlFresh2 :: m:Nat -> ρ:NameValuation p
                -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                -> d:Btwn 0 m -> w:Btwn 0 m
                -> i:{Btwn 0 m | wellTyped' (LEQLC (LBIN SUB e1 e2 d) 0 w i)
                              && wfE (LEQLC (LBIN SUB e1 e2 d) 0 w i)}
                -> σ:{WireValuation p m | freshE (LEQLC (LBIN SUB e1 e2 d) 0 w i) σ}
                -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}
                -> { freshE e2 σ1 } @-}
wgEqlFresh2 :: (Ord p, Fractional p) => Int -> NameValuation p
            -> LDSL p Int -> LDSL p Int -> Int -> Int -> Int
            -> WireValuation p -> WireValuation p
            -> Proof
wgEqlFresh2 m ρ e1 e2 d w i σ σ1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- if agree_Λ2(ρ,σ2) then also agree_Λ'(ρ,σ') ----------------------------------
{-@ agreeLemmaEQL :: m0:Nat -> m1:{Nat | m1 >= m0} -> m2:{Nat | m2 >= m1} -> m:{Nat | m >= m2}
                  -> p1:DSL p
                  -> p2:{DSL p | wellTyped (BIN EQL p1 p2)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> σ:WireValuation p m0

                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> λ2:LabelEnv p (Btwn 0 m2)

                  -> p1':{LDSL p (Btwn 0 m1) | wfE p1' && freshE p1' σ
                                            && label' p1 m0 λ  = (m1, p1', λ1)}
                  -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ  p1'}

                  -> p2':{LDSL p (Btwn 0 m2) | wfE p2' && freshE p2' σ1
                                            && label' p2 m1 λ1 = (m2, p2', λ2)}
                  -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 p2'}

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> e':{LDSL p (Btwn 0 m) | label' (BIN EQL p1 p2) m0 λ = (m, e', λ')}
                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}

                  -> Agree λ2 ρ σ2
                  -> Agree λ' ρ σ' @-}
agreeLemmaEQL :: (Fractional p, Ord p)
              => Int -> Int -> Int -> Int -> DSL p -> DSL p
              -> NameValuation p
              -> LabelEnv p Int
              -> WireValuation p

              -> LabelEnv p Int -> LabelEnv p Int
              -> LDSL p Int -> WireValuation p -> LDSL p Int -> WireValuation p
              -> LabelEnv p Int -> LDSL p Int -> WireValuation p

              -> (Var -> Proof)
              -> (Var -> Proof)
agreeLemmaEQL m0 m1 m2 m p1 p2 ρ λ σ λ1 λ2 p1' σ1 p2' σ2 λ' e' σ' π2 =
  agreeLemmaEQLC m0 (m2+1) m 0 (BIN SUB p1 p2) ρ λ λ2 σ λ' (LBIN SUB p1' p2' m2)
                 e' σ' (M.insert m2 (v1-v2) σ2)
                 (\y -> notElemLemma y m2 λ2 ?? π2 y)
  where v1 = labelType p1 m0 λ  m1 p1' λ1 ?? wgClosed m ρ σ  p1' σ1 ?? M.lookup' (outputWire p1') σ1
        v2 = labelType p2 m1 λ1 m2 p2' λ2 ?? wgClosed m ρ σ1 p2' σ2 ?? M.lookup' (outputWire p2') σ2
