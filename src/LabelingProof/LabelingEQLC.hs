{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--linear" @-}
{-@ LIQUID "--eliminate=all" @-}

{-@ LIQUID "--cores=1" @-}

module LabelingProof.LabelingEQLC where

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

-- if witnessGen succeeds for e1==0, it also succeeds for e1 -------------------
{-@ σ1Isk :: m1:Nat -> m:{Nat | m >= m1}
          -> ρ:NameValuation p -> σ:WireValuation p m1
          -> e1:LDSL p (Btwn 0 m1) -> k:p
          -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LEQLC e1 k w i
                                      && wfE e && freshE e σ}
          -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
          -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Isk :: (Ord p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> p -> Int -> Int
      -> LDSL p Int -> WireValuation p
      -> WireValuation p
σ1Isk m1 m ρ σ e1 k _w _i _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1


-- if fresh(e1==0, σ), then also fresh(e1,σ) -----------------------------------
{-@ wgIskFresh1 :: m:Nat
                -> e1:LDSL p (Btwn 0 m) -> k:p
                -> w:Btwn 0 m -> i:Btwn 0 m
                -> σ:{WireValuation p m | freshE (LEQLC e1 k w i) σ}
                -> { freshE e1 σ } @-}
wgIskFresh1 :: (Ord p, Fractional p)
            => Int -> LDSL p Int -> p -> Int -> Int -> WireValuation p -> Proof
wgIskFresh1 m e1 k w i σ = trivial


-- if e1↝e1' and e1==k↝e' then ∃w,i . e' = LEQLC e1' k w i ---------------------
{-@ labelIsk :: m0:Nat -> e1:DSL p -> λ:LabelEnv p (Btwn 0 m0) -> k:p

             -> m1:{Int | m1 >= m0}
             -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

             -> m:{Int | m >= m1}
             -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) |
                             label' (UN (EQLC k) e1) m0 λ = (m, e', λ')}
             -> (w::Btwn 0 m, i:{Btwn 0 m | e' = LEQLC e1' k w i}) @-}
labelIsk :: (Num p, Ord p) => Int -> DSL p -> LabelEnv p Int -> p
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> (Int, Int)
labelIsk m0 e1 λ k m1 e1' λ1 _m e' _λ' = case e' of
  LEQLC _ _ w i -> (w, i)


-- if agree_Λ1(ρ,σ1) then also agree_Λ'(ρ,σ') ----------------------------------
{-@ agreeLemmaEQLC :: m0:Nat -> m1:{Nat | m1 >= m0} -> m:{Nat | m >= m1}
                  -> k:p
                  -> p1:{DSL p | wellTyped (UN (EQLC k) p1)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> σ:WireValuation p m0

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ = (m1, p1', λ1)}
                  -> e':{LDSL p (Btwn 0 m) | label' (UN (EQLC k) p1) m0 λ = (m, e', λ')}
                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}
                  -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ p1'}

                  -> Agree λ1 ρ σ1

                  -> Agree λ' ρ σ' @-}
agreeLemmaEQLC :: (Fractional p, Eq p, Ord p)
              =>  Int -> Int -> Int -> p -> DSL p
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
agreeLemmaEQLC _m0 _m1 _m k p1 ρ _λ λ1 _σ _λ' _p1' e' σ' σ1 π1
 = \x -> π1 x ? notElemLemma x i λ1 ? notElemLemma x w λ1
  where (LEQLC _ _ w i) = e'
