{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module LabelingProof.LabelingLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import Utils
import TypeAliases

import Constraints
import DSL
import Label
import WitnessGeneration
import Semantics

import MapLemmas
import Language.Haskell.Liquid.ProofCombinators

{-@ label1Inc :: op:UnOp p -> e1:{DSL p | wellTyped (UN op e1)} -> m0:Nat -> λ:LabelEnv p Int
              -> m1:Int -> e1':LDSL p Int -> λ1:{LabelEnv p Int | label' e1 m0 λ = (m1, mkList1 e1', λ1)}
              ->  m:Int ->  e':LDSL p Int -> λ':{LabelEnv p Int | label' (UN op e1) m0 λ = (m, mkList1 e', λ')}
              -> {m >= m1} @-}
label1Inc :: Num p => UnOp p -> DSL p -> Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
label1Inc op _ _ _ _ _ _ _ _ _ = case op of
  BoolToF -> ()
  ISZERO  -> ()
  EQLC _  -> ()
  _       -> ()

{-@ label2Inc :: op:{BinOp p | desugaredBinOp op || op == DIV}
              -> e1:DSL p -> e2:{DSL p | wellTyped (BIN op e1 e2)}
              -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

              -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
              -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, mkList1 e1', λ1)}

              -> m2:Nat -> e2':LDSL p (Btwn 0 m2)
              -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, mkList1 e2', λ2)}

              ->  m:Nat ->  e':LDSL p (Btwn 0 m)
              -> λ':{LabelEnv p (Btwn 0 m) | label' (BIN op e1 e2) m0 λ = (m, mkList1 e', λ')}
              -> {m > m2 && m2 >= m1} @-}
label2Inc :: (Num p, Ord p) => BinOp p -> DSL p -> DSL p -> Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
label2Inc op e1 e2 m0 λ m1 _e1' λ1 m2 _e2' _λ2 m _e' _λ'
  = trivial ? case label' e1 m0 λ  of (m1,_,_) -> m1
            ? case label' e2 m1 λ1 of (m2,_,_) -> m2
            ? case op of
                DIV -> liquidAssert (m == m2+2)
                _   -> liquidAssert (m == m2+1)


-- ∀x ∈ dom(Λ) . ρ(x) = σ(Λ(x))
{-@ type Composable Ρ Λ Σ = var:{String | elem' var (M.keys Λ)}
                         -> {(M.lookup var Ρ = M.lookup (M.lookup' var Λ) Σ)} @-}
