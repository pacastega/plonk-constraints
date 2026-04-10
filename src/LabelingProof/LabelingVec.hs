{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module LabelingProof.LabelingVec where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import Utils
import TypeAliases

import DSL
import Label
import WitnessGeneration
import Semantics

import MapLemmas
import LabelingProof.LabelingLemmas
import WitnessGenProof.WitnessGenLemmas
import Language.Haskell.Liquid.ProofCombinators


{-@ labelIncCons :: e1:DSL p -> e2:{DSL p | wellTyped (CONS e1 e2)}
                 -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

                 -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
                 -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

                 -> m2:Nat -> e2':LDSL p (Btwn 0 m2)
                 -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                 -> m:Nat -> e':LDSL p (Btwn 0 m)
                 -> λ':{LabelEnv p (Btwn 0 m) | label' (CONS e1 e2) m0 λ = (m, e', λ')}
                 -> { m >= m2 && m2 >= m1 } @-}
labelIncCons :: (Num p, Ord p) => DSL p -> DSL p -> Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Proof
labelIncCons e1 e2 m0 λ m1 _e1' λ1 m2 _e2' _λ2 m _e' _λ'
  = trivial ? case label' e1 m0 λ  of (m1,_,_) -> m1
            ? case label' e2 m1 λ1 of (m2,_,_) -> m2


-- if witnessGen succeeds for e1::e2, it also succeeds for e1 and e2 -----------
{-@ σ1Cons :: m1:Nat -> m:{Nat | m >= m1}
           -> ρ:NameValuation p -> σ:WireValuation p m1
           -> e1:LDSL p (Btwn 0 m1) -> e2:LDSL p (Btwn 0 m)
           -> e:{TypedLDSL p (Btwn 0 m) | e = LCONS e1 e2
                                      && wfE e && freshE e σ}
           -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
           -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Cons     :: (Ord p, Fractional p) => Int -> Int
       -> NameValuation p -> WireValuation p
       -> LDSL p Int -> LDSL p Int
       -> LDSL p Int -> WireValuation p
       -> WireValuation p
σ1Cons m1 m ρ σ e1 _e2 _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1

{-@ σ2Cons :: m2:Nat -> m:{Nat | m >= m2}
           -> ρ:NameValuation p -> σ:WireValuation p m2
           -> e1:LDSL p (Btwn 0 m2) -> e2:LDSL p (Btwn 0 m2)
           -> e:{TypedLDSL p (Btwn 0 m) | e = LCONS e1 e2
                                      && wfE e && freshE e σ}
           -> {σ':WireValuation p m  | Just σ' = witnessGenE' m  ρ σ  e}
           -> {σ1:WireValuation p m2 | Just σ1 = witnessGenE' m  ρ σ  e1}
           -> {σ2:WireValuation p m2 | Just σ2 = witnessGenE' m  ρ σ1 e2} @-}
σ2Cons     :: (Ord p, Fractional p) => Int -> Int
       -> NameValuation p -> WireValuation p
       -> LDSL p Int -> LDSL p Int
       -> LDSL p Int -> WireValuation p -> WireValuation p
       -> WireValuation p
σ2Cons m2 m ρ σ e1 e2 _e _σ' _σ1 =
  wgLemma m2 m ρ σ e1 ?? case witnessGenE' m2 ρ σ e1 of
    Just σ1 -> wgLemma m2 m ρ σ1 e2 ?? case witnessGenE' m2 ρ σ1 e2 of
      Just σ2 -> σ2


-- if fresh(e1::e2, σ), then also fresh(e1,σ) and fresh(e2,σ1) -----------------
{-@ wgConsFresh1 :: m:Nat
                 -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                 -> σ:{WireValuation p m | freshE (LCONS e1 e2) σ}
                 -> { freshE e1 σ } @-}
wgConsFresh1 :: (Ord p, Fractional p) => Int
             -> LDSL p Int -> LDSL p Int
             -> WireValuation p
             -> Proof
wgConsFresh1 m e1 e2 σ = trivial

{-@ wgConsFresh2 :: m:Nat -> ρ:NameValuation p
                 -> e1:LDSL p (Btwn 0 m)
                 -> e2:{LDSL p (Btwn 0 m) | wellTyped' (LCONS e1 e2)
                                         && wfE (LCONS e1 e2)}
                 -> σ:{WireValuation p m | freshE (LCONS e1 e2) σ}
                 -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}
                 -> { freshE e2 σ1 } @-}
wgConsFresh2 :: (Ord p, Fractional p) => Int -> NameValuation p
             -> LDSL p Int -> LDSL p Int
             -> WireValuation p -> WireValuation p
             -> Proof
wgConsFresh2 m ρ e1 e2 σ σ1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- if e1::e2 is well-typed and well-formed, then so are e1 and e2 --------------
{-@ wfCons :: e1:LDSL p Int
           -> e2:{LDSL p Int | wfE (LCONS e1 e2) && wellTyped' (LCONS e1 e2)}
           -> { wfE e1 && wfE e2 && wellTyped' e1 && wellTyped' e2 } @-}
wfCons :: LDSL p Int -> LDSL p Int -> Proof
wfCons e1 e2 = trivial


-- if e1↝e1', e2↝e2' and e1::e2↝e' then e' = LCONS e1' e2' ---------------------
{-@ labelCons :: m0:Nat -> e1:DSL p -> e2:DSL p -> λ:LabelEnv p (Btwn 0 m0)

              -> m1:{Int | m1 >= m0}
              -> e1':LDSL p (Btwn 0 m1)
              -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

              -> m2:{Int | m2 >= m1}
              -> e2':LDSL p (Btwn 0 m2)
              -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

              -> m:{Int | m >= m2}
              -> e':LDSL p (Btwn 0 m)
              -> λ':{LabelEnv p (Btwn 0 m) |
                              label' (CONS e1 e2) m0 λ = (m, e', λ')}
              -> { e' = LCONS e1' e2' } @-}
labelCons :: (Num p, Ord p) => Int -> DSL p -> DSL p -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
labelCons m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 _m e' _λ' = case e' of
   LCONS _ _ -> trivial


-- if agree_Λ2(ρ,σ2) then also agree_Λ'(ρ,σ') [CONS] ---------------------------
{-@ agreeLemmaCons :: m0:Nat -> m1:{Nat | m1 >= m0} -> m2:{Nat | m2 >= m1} -> m:{Nat | m >= m2}
                   -> p1:DSL p -> p2:DSL p
                   -> ρ:NameValuation p
                   -> λ:LabelEnv p (Btwn 0 m0)
                   -> λ1:LabelEnv p (Btwn 0 m1)
                   -> λ2:LabelEnv p (Btwn 0 m2)
                   -> σ:WireValuation p m0

                   -> Agree λ ρ σ

                   -> λ':LabelEnv p (Btwn 0 m)
                   -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ  = (m1, p1', λ1)}
                   -> p2':{LDSL p (Btwn 0 m2) | label' p2 m1 λ1 = (m2, p2', λ2)}

                   -> e':{LDSL p (Btwn 0 m) | label' (CONS p1 p2) m0 λ = (m, e', λ')}
                   -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ  e'}
                   -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ  p1'}
                   -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 p2'}

                   -> Agree λ2 ρ σ2

                   -> Agree λ' ρ σ' @-}
agreeLemmaCons :: (Fractional p, Eq p, Ord p)
               => Int -> Int -> Int -> Int -> DSL p -> DSL p
               -> NameValuation p
               -> LabelEnv p Int -> LabelEnv p Int -> LabelEnv p Int
               -> WireValuation p

               -> (String -> Proof)

               -> LabelEnv p Int
               -> LDSL p Int -> LDSL p Int -> LDSL p Int
               -> WireValuation p -> WireValuation p -> WireValuation p

               -> (String -> Proof)

               -> (String -> Proof)
agreeLemmaCons m0 m1 m2 m p1 p2 ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 = π2


-- if agree_Λ(ρ,σ) then also agree_Λ'(ρ,σ') [NIL] ------------------------------
{-@ agreeLemmaNil :: m0:Nat -> m:{Nat | m >= m0} -> τ:Ty
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> σ:WireValuation p m0

                  -> Agree λ ρ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> e':{LDSL p (Btwn 0 m) | label' (NIL τ) m0 λ = (m, e', λ')}
                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ  e'}

                  -> Agree λ' ρ σ' @-}
agreeLemmaNil :: (Fractional p, Eq p, Ord p)
              => Int -> Int -> Ty
              -> NameValuation p -> LabelEnv p Int -> WireValuation p

              -> (String -> Proof)

              -> LabelEnv p Int -> LDSL p Int -> WireValuation p

              -> (String -> Proof)
agreeLemmaNil m0 m τ ρ λ σ π λ' e' σ' = π
