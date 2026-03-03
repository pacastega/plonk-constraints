{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

module WitnessGenProof.CompletenessOps where

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
import LabelingProof.LabelingLemmas

import Language.Haskell.Liquid.ProofCombinators


{-@ wgCompleteBin :: m0:Nat -> m1:{Nat | m1 >= m0} -> m2:{Nat | m2 >= m1} -> m:{Nat | m >= m2}
                  -> op:BinOp' p
                  -> e1:{DSL p | True}
                  -> e2:{DSL p | wellTyped (BIN op e1 e2)}
                  -> ρ:{NameValuation p | isJust (eval (BIN op e1 e2) ρ)}
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> σ:WireValuation p m0

                  -> Agree λ ρ σ

                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> λ2:LabelEnv p (Btwn 0 m2)

                  -> σ1:WireValuation p m1

                  -> e1':{LDSL p (Btwn 0 m1) | freshE e1' σ && wfE e1'
                                      && label' e1 m0 λ = (m1, mkList1 e1', λ1)
                                      && witnessGenE' m ρ σ e1' = Just σ1}

                  -> e2':{LDSL p (Btwn 0 m2) | freshE e2' σ1 && wfE e2'
                                      && label' e2 m1 λ1 = (m2, mkList1 e2', λ2)
                                      && isJust (witnessGenE' m ρ σ1 e2')}

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> e':{LDSL p (Btwn 0 m) | freshE e' σ && wfE e'
                        && label' (BIN op e1 e2) m0 λ = (m, mkList1 e', λ')}

                  -> { isJust (witnessGenE' m ρ σ e') } @-}

wgCompleteBin :: (Fractional p, Ord p)
              => Int -> Int -> Int -> Int -> BinOp p -> DSL p -> DSL p
              -> NameValuation p -> LabelEnv p Int -> WireValuation p

              -> (Var -> Proof)

              -> LabelEnv p Int -> LabelEnv p Int
              -> WireValuation p
              -> LDSL p Int -> LDSL p Int

              -> LabelEnv p Int -> LDSL p Int

              -> Proof
wgCompleteBin m0 m1 m2 m op e1 e2 ρ λ σ π λ1 λ2 σ1 e1' e2' λ' e' =
  case witnessGenE' m ρ σ1 e2' of
    Just _ -> case op of
      ADD         -> liquidAssert (e' == LBIN op e1' e2' m2)
      SUB         -> liquidAssert (e' == LBIN op e1' e2' m2)
      MUL         -> liquidAssert (e' == LBIN op e1' e2' m2)
      LINCOMB _ _ -> liquidAssert (e' == LBIN op e1' e2' m2)
      AND         -> liquidAssert (e' == LBIN op e1' e2' m2)
      OR          -> liquidAssert (e' == LBIN op e1' e2' m2)
      XOR         -> liquidAssert (e' == LBIN op e1' e2' m2)
      UnsafeAND   -> liquidAssert (e' == LBIN op e1' e2' m2)
      UnsafeOR    -> liquidAssert (e' == LBIN op e1' e2' m2)
      UnsafeXOR   -> liquidAssert (e' == LBIN op e1' e2' m2)


{-@ evalJustIH :: e1:DSL p -> e2:DSL p -> op:{BinOp' p | wellTyped (BIN op e1 e2)}
               -> ρ:{NameValuation p | isJust (eval (BIN op e1 e2) ρ)}
               -> { isJust (eval e1 ρ) && isJust (eval e2 ρ)} @-}
evalJustIH :: (Fractional p, Ord p) => DSL p -> DSL p -> BinOp p
           -> NameValuation p -> Proof
evalJustIH e1 e2 op ρ = case (eval e1 ρ, eval e2 ρ) of
  (Just _, Just _) -> trivial


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
