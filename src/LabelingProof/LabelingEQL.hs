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


-- if witnessGen succeeds for e1==e2, it also succeeds for e1 and e2 -----------
{-@ σ1Eql :: m1:Nat -> m:{Nat | m >= m1}
          -> ρ:NameValuation p -> σ:WireValuation p m1
          -> e1:LDSL p (Btwn 0 m1) -> e2:LDSL p (Btwn 0 m)
          -> d:Btwn 0 m -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LEQLC (LBIN SUB e1 e2 d) 0 w i
                                      && wfE e && freshE e σ}
          -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
          -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Eql :: (Ord p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> Int -> Int -> Int
      -> LDSL p Int -> WireValuation p
      -> WireValuation p
σ1Eql m1 m ρ σ e1 _e2 _d _w _i _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1

{-@ σ2Eql :: m2:Nat -> m:{Nat | m >= m2}
          -> ρ:NameValuation p -> σ:WireValuation p m2
          -> e1:LDSL p (Btwn 0 m2) -> e2:LDSL p (Btwn 0 m2)
          -> d:Btwn 0 m -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LEQLC (LBIN SUB e1 e2 d) 0 w i
                                      && wfE e && freshE e σ}
          -> {σ':WireValuation p m  | Just σ' = witnessGenE' m  ρ σ  e}
          -> {σ1:WireValuation p m2 | Just σ1 = witnessGenE' m  ρ σ  e1}
          -> {σ2:WireValuation p m2 | Just σ2 = witnessGenE' m  ρ σ1 e2} @-}
σ2Eql :: (Ord p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> Int -> Int -> Int
      -> LDSL p Int -> WireValuation p -> WireValuation p
      -> WireValuation p
σ2Eql m2 m ρ σ e1 e2 _d _w _i _e _σ' _σ1 =
  wgLemma m2 m ρ σ e1 ?? case witnessGenE' m2 ρ σ e1 of
    Just σ1 -> wgLemma m2 m ρ σ1 e2 ?? case witnessGenE' m2 ρ σ1 e2 of
      Just σ2 -> σ2


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


-- if e1==e2 is well-typed and well-formed, then so are e1 and e2 --------------
{-@ wfEql :: e1:LDSL p Int -> e2:LDSL p Int -> d:Int -> w:Int
          -> i:{Int | wfE        (LEQLC (LBIN SUB e1 e2 d) 0 w i)
                   && wellTyped' (LEQLC (LBIN SUB e1 e2 d) 0 w i)}
          -> { wfE e1 && wfE e2 && wellTyped' e1 && wellTyped' e2 } @-}
wfEql :: (Num p) => LDSL p Int -> LDSL p Int -> Int -> Int -> Int -> Proof
wfEql e1 e2 d w i = trivial


-- if e1↝e1', e2↝e2' and e1==e2↝e' then ∃d,w,i . e' = LEQLC (LBIN SUB e1' e2' d) 0 w i
{-@ labelEql :: m0:Nat -> e1:DSL p -> e2:DSL p -> λ:LabelEnv p (Btwn 0 m0)

             -> m1:{Int | m1 >= m0}
             -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

             -> m2:{Int | m2 >= m1}
             -> e2':LDSL p (Btwn 0 m2)
             -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

             -> m:{Int | m >= m2}
             -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) |
                             label' (BIN EQL e1 e2) m0 λ = (m, e', λ')}
             -> (d::Btwn 0 m, w::Btwn 0 m, i:{Btwn 0 m | e' = LEQLC (LBIN SUB e1' e2' d) 0 w i}) @-}
labelEql :: (Num p, Ord p) => Int -> DSL p -> DSL p -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> (Int, Int, Int)
labelEql m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 _m e' _λ' = case e' of
  LEQLC (LBIN SUB _ _ d) _ w i -> (d, w, i)


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
