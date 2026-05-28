{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.UniquenessOps where

import Constraints
import TypeAliases
import DSL
import Semantics
import Label
import WitnessGeneration

import Utils

import BooleanProof

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import MapLemmas
import LabelingProof.LabelingLemmas
import LabelingProof.RecursiveLemmas
import WitnessGenProof.WitnessGenLemmas
import WitnessGenProof.SemanticsLemmas
import WitnessGenProof.UniquenessLemmas
import WitnessGenProof.UniquenessLemmas2

import WitnessGenProof.UniquenessBase

import Language.Haskell.Liquid.ProofCombinators



{-@ uniqueUn :: m0:Nat -> m':Nat -> op:UnOp p -> e1:DSL p
             -> e:{TypedDSL p | e = UN op e1}
             -> ρ:NameValuation p
             -> λ:LabelEnv p (Btwn 0 m0)

             -> m1:{Nat | m0 <= m1}
             -> e1':{TypedLDSL p (Btwn 0 m1) | wfE e1'}
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

             -> m:{Nat | m0 <= m && m <= m'}
             -> e':{TypedLDSL p (Btwn 0 m) | wfE e'}
             -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

             -> {σ:WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
             -> v1:{DSLValue p | evalWire m' e1' σ = v1 && eval e1 ρ = Just v1}
             -> v: {DSLValue p | evalWire m' e'  σ = v}

             -> { eval e ρ = Just v } @-}
uniqueUn :: (Fractional p, Ord p) => Int -> Int -> UnOp p -> DSL p
         -> DSL p -> NameValuation p -> LabelEnv p Int

         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> WireValuation p -> DSLValue p -> DSLValue p

         -> Proof
uniqueUn m0 m' op e1 e ρ λ m1 e1' λ1 m e' λ' σ v1 v =
  case op of
    ISZERO -> evalWireScalar m' e1' σ
           ?? liquidAssert (v' == eqlFn 0 v1')
           where v1' = M.lookup' (outputWire e1') σ
                 v'  = M.lookup' (outputWire e')  σ
    EQLC k -> evalWireScalar m' e1' σ
           ?? liquidAssert (v' == eqlFn k v1')
           where v1' = M.lookup' (outputWire e1') σ
                 v'  = M.lookup' (outputWire e')  σ
    BoolToF -> evalWireScalar m' e1' σ
    _ -> evalWireScalar m' e1' σ


{-@ uniqueBin :: m0:Nat -> m':Nat -> op:BinOp p -> e1:DSL p -> e2:DSL p
              -> e:{TypedDSL p | e = BIN op e1 e2}
              -> ρ:NameValuation p
              -> λ:LabelEnv p (Btwn 0 m0)

              -> m1:{Nat | m0 <= m1}
              -> e1':{TypedLDSL p (Btwn 0 m1) | wfE e1'}
              -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

              -> m2:{Nat | m1 <= m2}
              -> e2':{TypedLDSL p (Btwn 0 m2) | wfE e2'}
              -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

              -> m:{Nat | m0 <= m && m <= m'}
              -> e':{TypedLDSL p (Btwn 0 m) | wfE e'}
              -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

              -> {σ:WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
              -> v1:{DSLValue p | evalWire m' e1' σ = v1 && eval e1 ρ = Just v1}
              -> v2:{DSLValue p | evalWire m' e2' σ = v2 && eval e2 ρ = Just v2}
              -> v: {DSLValue p | evalWire m' e'  σ = v}

              -> { eval e ρ = Just v } @-}
uniqueBin :: (Fractional p, Ord p) => Int -> Int -> BinOp p -> DSL p -> DSL p
          -> DSL p -> NameValuation p -> LabelEnv p Int

          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> WireValuation p -> DSLValue p -> DSLValue p -> DSLValue p

          -> Proof
uniqueBin m0 m' op e1 e2 e ρ λ m1 e1' λ1 m2 e2' λ2 m e' λ' σ v1 v2 v =
  case op of
    EQL -> evalWireScalar m' e1' σ
        ?? evalWireScalar m' e2' σ
        ?? liquidAssert (v' == eqlFn v1' v2')
        where v1' = M.lookup' (outputWire e1') σ
              v2' = M.lookup' (outputWire e2') σ
              v'  = M.lookup' (outputWire e')  σ
    DIV -> evalWireScalar m' e1' σ
        ?? evalWireScalar m' e2' σ
    _ -> evalWireScalar m' e1' σ
      ?? evalWireScalar m' e2' σ

{-@ uniqueCons :: m0:Nat -> m':Nat -> e1:DSL p -> e2:DSL p
               -> e:{TypedDSL p | e = CONS e1 e2}
               -> ρ:NameValuation p
               -> λ:LabelEnv p (Btwn 0 m0)

               -> m1:{Nat | m0 <= m1}
               -> e1':{TypedLDSL p (Btwn 0 m1) | wfE e1'}
               -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

               -> m2:{Nat | m1 <= m2}
               -> e2':{TypedLDSL p (Btwn 0 m2) | wfE e2'}
               -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

               -> m:{Nat | m0 <= m && m <= m'}
               -> e':{TypedLDSL p (Btwn 0 m) | wfE e'}
               -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

               -> {σ:WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
               -> v1:{DSLValue p | evalWire m' e1' σ = v1 && eval e1 ρ = Just v1}
               -> v2:{DSLValue p | evalWire m' e2' σ = v2 && eval e2 ρ = Just v2}
               -> v: {DSLValue p | evalWire m' e'  σ = v}

               -> { eval e ρ = Just v } @-}
uniqueCons :: (Fractional p, Ord p) => Int -> Int -> DSL p -> DSL p
           -> DSL p -> NameValuation p -> LabelEnv p Int

           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> WireValuation p -> DSLValue p -> DSLValue p -> DSLValue p

           -> Proof
uniqueCons m0 m' e1 e2 e ρ λ m1 e1' λ1 m2 e2' λ2 m e' λ' σ v1 v2 v = trivial
