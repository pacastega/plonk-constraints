{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module LabelingProof.RecursiveLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import TypeAliases
import DSL
import Utils
import WitnessGeneration
import Label

import WitnessGenProof.WitnessGenLemmas

import Language.Haskell.Liquid.ProofCombinators

{-@ wellTypedBin :: e1:DSL p -> e2:DSL p
                 -> op:{BinOp p | wellTyped (BIN op e1 e2)}
                 -> { wellTyped e1 && wellTyped e2 } @-}
wellTypedBin :: DSL p -> DSL p -> BinOp p -> Proof
wellTypedBin e1 e2 op = trivial

{-@ σ1Div :: m1:Nat -> m:{Nat | m >= m1}
          -> ρ:NameValuation p -> σ:WireValuation p m1
          -> e1:LDSL p (Btwn 0 m1) -> e2:LDSL p (Btwn 0 m)
          -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LDIV e1 e2 w i
                                      && wfE e && freshE e σ}
          -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
          -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Div :: (Ord p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> Int -> Int
      -> LDSL p Int -> WireValuation p
      -> WireValuation p
σ1Div m1 m ρ σ e1 _e2 _w _i _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1


{-@ σ2Div :: m2:Nat -> m:{Nat | m >= m2}
          -> ρ:NameValuation p -> σ:WireValuation p m2
          -> e1:LDSL p (Btwn 0 m2) -> e2:LDSL p (Btwn 0 m2)
          -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LDIV e1 e2 w i
                                      && wfE e && freshE e σ}
          -> {σ':WireValuation p m  | Just σ' = witnessGenE' m  ρ σ  e}
          -> {σ1:WireValuation p m2 | Just σ1 = witnessGenE' m  ρ σ  e1}
          -> {σ2:WireValuation p m2 | Just σ2 = witnessGenE' m  ρ σ1 e2} @-}
σ2Div :: (Ord p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> Int -> Int
      -> LDSL p Int -> WireValuation p -> WireValuation p
      -> WireValuation p
σ2Div m2 m ρ σ e1 e2 _w _i _e _σ' _σ1 =
  wgLemma m2 m ρ σ e1 ?? case witnessGenE' m2 ρ σ e1 of
    Just σ1 -> wgLemma m2 m ρ σ1 e2 ?? case witnessGenE' m2 ρ σ1 e2 of
      Just σ2 -> σ2


{-@ wgDivFresh1 :: m:Nat
                -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                -> w:Btwn 0 m -> i:Btwn 0 m
                -> σ:{WireValuation p m | freshE (LDIV e1 e2 w i) σ}
                -> { freshE e1 σ } @-}
wgDivFresh1 :: (Ord p, Fractional p) => Int
            -> LDSL p Int -> LDSL p Int -> Int -> Int
            -> WireValuation p
            -> Proof
wgDivFresh1 m e1 e2 w i σ = trivial


{-@ wgDivFresh2 :: m:Nat -> ρ:NameValuation p
                -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                -> w:Btwn 0 m -> i:{Btwn 0 m | wellTyped' (LDIV e1 e2 w i)
                                            && wfE (LDIV e1 e2 w i)}
                -> σ:{WireValuation p m | freshE (LDIV e1 e2 w i) σ}
                -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}
                -> { freshE e2 σ1 } @-}
wgDivFresh2 :: (Ord p, Fractional p) => Int -> NameValuation p
            -> LDSL p Int -> LDSL p Int -> Int -> Int
            -> WireValuation p -> WireValuation p
            -> Proof
wgDivFresh2 m ρ e1 e2 w i σ σ1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


{-@ wfDiv :: e1:LDSL p Int -> e2:LDSL p Int -> w:Int
          -> i:{Int | wfE (LDIV e1 e2 w i) && wellTyped' (LDIV e1 e2 w i)}
          -> { wfE e1 && wfE e2 && wellTyped' e1 && wellTyped' e2 } @-}
wfDiv :: LDSL p Int -> LDSL p Int -> Int -> Int -> Proof
wfDiv e1 e2 w i = trivial


{-@ labelDiv :: m0:Nat -> e1:DSL p -> e2:DSL p -> λ:LabelEnv p (Btwn 0 m0)

             -> m1:{Int | m1 >= m0}
             -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

             -> m2:{Int | m2 >= m1}
             -> e2':LDSL p (Btwn 0 m2)
             -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

             -> m:{Int | m >= m2}
             -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) |
                             label' (BIN DIV e1 e2) m0 λ = (m, e', λ')}
             -> (w::Btwn 0 m, i:{Btwn 0 m | e' = LDIV e1' e2' w i}) @-}
labelDiv :: (Num p, Ord p) => Int -> DSL p -> DSL p -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> (Int, Int)
labelDiv m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 _m e' _λ' = case e' of
  LDIV _ _ w i -> (w, i)


-- {-@ wgBinOp :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
--             -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
--             -> op:BinOp p -> i:Btwn 0 m
--             -> e:{TypedLDSL p (Btwn 0 m) | e = BIN op e1 e2 i
--                                         && wfE e && freshE e σ}
--             -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
--             -> ( σ1::{σ1:WireValuation p | Just σ1 = witnessGenE' m ρ σ e1}
--                , {σ2:WireValuation p | Just σ2 = witnessGenE' m ρ σ1 e2}) @-}
-- wgBinOp :: (Ord p, Fractional p) => Int -> NameValuation p -> WireValuation p
--         -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
--         -> LDSL p Int -> WireValuation p
--         -> (WireValuation p, WireValuation p)
-- wgBinOp m ρ σ e1 e2 op e σ' = case op of


-- workarounds to fix "crash: unknown constant"

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
