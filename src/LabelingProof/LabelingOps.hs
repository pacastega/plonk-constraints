{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module LabelingProof.LabelingOps where

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

-- UNARY OPERATORS =============================================================

-- if fresh(e1==0, σ), then also fresh(e1,σ) -----------------------------------
{-@ wgUnFresh1 :: m:Nat
               -> e1:LDSL p (Btwn 0 m) -> op:UnOp' p
               -> i:Btwn 0 m
               -> σ:{WireValuation p m | freshE (LUN op e1 i) σ}
               -> { freshE e1 σ } @-}
wgUnFresh1 :: (Ord p, Fractional p)
           => Int -> LDSL p Int -> UnOp p -> Int -> WireValuation p -> Proof
wgUnFresh1 m e1 op i σ = trivial


-- if agree_Λ1(ρ,σ1) then also agree_Λ'(ρ,σ1) ----------------------------------
{-@ agreeLemmaUn  :: m0:Nat -> m1:{Nat | m1 >= m0} -> m:{Nat | m >= m1}
                  -> p1:DSL p
                  -> op:{UnOp' p | wellTyped (UN op p1)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> σ:WireValuation p m0

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ = (m1, p1', λ1)}
                  -> e':{LDSL p (Btwn 0 m) | label' (UN op p1) m0 λ = (m, e', λ')}
                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}
                  -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ p1'}

                  -> Agree λ1 ρ σ1

                  -> Agree λ' ρ σ' @-}
agreeLemmaUn :: (Fractional p, Eq p, Ord p)
             => Int -> Int -> Int -> DSL p -> UnOp p
             -> NameValuation p
             -> LabelEnv p Int
             -> LabelEnv p Int
             -> WireValuation p

             -> LabelEnv p Int
             -> LDSL p Int
             -> LDSL p Int
             -> WireValuation p
             -> WireValuation p

             -> (String -> Proof)

             -> (String -> Proof)
agreeLemmaUn m0 m1 m p1 op ρ λ λ1 σ λ' p1' e' σ' σ1 π1 =
  labelType (UN op p1) m0 λ m e' λ' ?? case op of
  ADDC k -> \x -> π1 x ? notElemLemma x (outputWire e') λ1
  MULC k -> \x -> π1 x ? notElemLemma x (outputWire e') λ1

  NOT ->       \x -> π1 x ? notElemLemma x (outputWire e') λ1
  UnsafeNOT -> \x -> π1 x ? notElemLemma x (outputWire e') λ1


-- BINARY OPERATORS ============================================================

-- if fresh(e1⮾e2, σ), then also fresh(e1,σ) and fresh(e2,σ1) ------------------
{-@ wgBinFresh1 :: m:Nat
                -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                -> op:BinOp' p -> i:Btwn 0 m
                -> σ:{WireValuation p m | freshE (LBIN op e1 e2 i) σ}
                -> { freshE e1 σ } @-}
wgBinFresh1 :: (Ord p, Fractional p) => Int
            -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
            -> WireValuation p
            -> Proof
wgBinFresh1 m e1 e2 op i σ = trivial

{-@ wgBinFresh2 :: m:Nat -> ρ:NameValuation p
                -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                -> op:BinOp' p -> i:{Btwn 0 m | wellTyped' (LBIN op e1 e2 i)
                                            && wfE (LBIN op e1 e2 i)}
                -> σ:{WireValuation p m | freshE (LBIN op e1 e2 i) σ}
                -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}
                -> { freshE e2 σ1 } @-}
wgBinFresh2 :: (Ord p, Fractional p) => Int -> NameValuation p
            -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
            -> WireValuation p -> WireValuation p
            -> Proof
wgBinFresh2 m ρ e1 e2 op i σ σ1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- if agree_Λ2(ρ,σ2) then also agree_Λ'(ρ,σ') ----------------------------------
{-@ agreeLemmaBin :: m0:Nat -> m1:{Nat | m1 >= m0} -> m2:{Nat | m2 >= m1} -> m:{Nat | m >= m2}
                  -> p1:DSL p
                  -> p2:DSL p
                  -> op:{BinOp' p | wellTyped (BIN op p1 p2)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> λ2:LabelEnv p (Btwn 0 m2)
                  -> σ:WireValuation p m0

                  -> Agree λ ρ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ  = (m1, p1', λ1)}
                  -> p2':{LDSL p (Btwn 0 m2) | label' p2 m1 λ1 = (m2, p2', λ2)}

                  -> e':{LDSL p (Btwn 0 m) | label' (BIN op p1 p2) m0 λ = (m, e', λ')}
                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ  e'}
                  -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ  p1'}
                  -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 p2'}

                  -> Agree λ2 ρ σ2

                  -> Agree λ' ρ σ' @-}
agreeLemmaBin :: (Fractional p, Eq p, Ord p)
              => Int -> Int -> Int -> Int -> DSL p -> DSL p -> BinOp p
              -> NameValuation p
              -> LabelEnv p Int -> LabelEnv p Int -> LabelEnv p Int
              -> WireValuation p

              -> (String -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int -> LDSL p Int -> LDSL p Int
              -> WireValuation p -> WireValuation p -> WireValuation p

              -> (String -> Proof)

              -> (String -> Proof)
agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 =
  labelType (BIN op p1 p2) m0 λ m e' λ' ?? case op of
  ADD           -> \x -> π2 x ? notElemLemma x (outputWire e') λ2
  SUB           -> \x -> π2 x ? notElemLemma x (outputWire e') λ2
  MUL           -> \x -> π2 x ? notElemLemma x (outputWire e') λ2
  LINCOMB k1 k2 -> \x -> π2 x ? notElemLemma x (outputWire e') λ2
  AND -> \x -> π2 x ? notElemLemma x (outputWire e') λ2
  OR  -> \x -> π2 x ? notElemLemma x (outputWire e') λ2
  XOR -> \x -> π2 x ? notElemLemma x (outputWire e') λ2
  UnsafeAND -> \x -> π2 x ? notElemLemma x (outputWire e') λ2
  UnsafeOR  -> \x -> π2 x ? notElemLemma x (outputWire e') λ2
  UnsafeXOR -> \x -> π2 x ? notElemLemma x (outputWire e') λ2


-- workarounds to fix "crash: unknown constant" ================================

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
