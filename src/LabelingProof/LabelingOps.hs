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
import Language.Haskell.Liquid.ProofCombinators

{-@ labelProofUn  :: m0:Nat -> m1:{Nat | m1 >= m0} -> m:{Nat | m >= m1}
                  -> p1:ScalarDSL p
                  -> op:{UnOp' p | wellTyped (UN op p1)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> σ:M.Map (Btwn 0 m0) p

                  -> Composable ρ λ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ = (m1, mkList1 p1', λ1)}
                  -> e':{LDSL p (Btwn 0 m) | label' (UN op p1) m0 λ = (m, mkList1 e', λ')}
                  -> σ':{M.Map (Btwn 0 m) p | Just σ' = witnessGenE' m ρ σ e'}
                  -> σ1:{M.Map (Btwn 0 m1) p | Just σ1 = witnessGenE' m ρ σ p1'}

                  -> v:p -> v1:{p | M.lookup (outputWire p1') σ1 == Just v1}

                  -> ({ eval p1 ρ = Just (VF v1) <=> M.lookup (outputWire p1') σ1 = Just v1 })
                  -> Composable ρ λ1 σ1

                  -> ({ eval (UN op p1) ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v },
                    Composable ρ λ' σ') @-}
labelProofUn :: (Fractional p, Eq p, Ord p)
              => Int -> Int -> Int -> DSL p -> UnOp p
              -> NameValuation p
              -> LabelEnv p Int
              -> LabelEnv p Int
              -> M.Map Int p

              -> (String -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int
              -> LDSL p Int
              -> M.Map Int p
              -> M.Map Int p

              -> p -> p
              -> Proof -> (String -> Proof)

              -> (Proof, String -> Proof)
labelProofUn m0 m1 m p1 op ρ λ λ1 σ π λ' p1' e' σ' σ1 v v1 ih1 π1 = case op of
  ADDC k -> ((), \x -> π1 x ? notElemLemma' x (outputWire e') λ1)
  MULC k -> ((), \x -> π1 x ? notElemLemma' x (outputWire e') λ1)

  NOT ->       ((), \x -> π1 x ? notElemLemma' x (outputWire e') λ1)
  UnsafeNOT -> ((), \x -> π1 x ? notElemLemma' x (outputWire e') λ1)


{-@ labelProofBin :: m0:Nat -> m1:{Nat | m1 >= m0} -> m2:{Nat | m2 >= m1} -> m:{Nat | m >= m2}
                  -> p1:ScalarDSL p
                  -> p2:ScalarDSL p
                  -> op:{BinOp' p | wellTyped (BIN op p1 p2)}
                  -> ρ:NameValuation p
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> λ1:LabelEnv p (Btwn 0 m1)
                  -> λ2:LabelEnv p (Btwn 0 m2)
                  -> σ:M.Map (Btwn 0 m0) p

                  -> Composable ρ λ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> p1':{LDSL p (Btwn 0 m1) | label' p1 m0 λ  = (m1, mkList1 p1', λ1)}
                  -> p2':{LDSL p (Btwn 0 m2) | label' p2 m1 λ1 = (m2, mkList1 p2', λ2)}

                  -> e':{LDSL p (Btwn 0 m) | label' (BIN op p1 p2) m0 λ = (m, mkList1 e', λ')}
                  -> σ':{M.Map (Btwn 0 m) p | Just σ' = witnessGenE' m ρ σ e'}
                  -> σ1:{M.Map (Btwn 0 m1) p | Just σ1 = witnessGenE' m ρ σ p1'}
                  -> σ2:{M.Map (Btwn 0 m2) p | Just σ2 = witnessGenE' m ρ σ1 p2'}

                  -> v:p
                  -> v1:{p | M.lookup (outputWire p1') σ1 == Just v1}
                  -> v2:{p | M.lookup (outputWire p2') σ2 == Just v2}

                  -> ({ eval p1 ρ = Just (VF v1) <=> M.lookup (outputWire p1') σ1 = Just v1 })
                  -> Composable ρ λ1 σ1

                  -> ({ eval p2 ρ = Just (VF v2) <=> M.lookup (outputWire p2') σ2 = Just v2 })
                  -> Composable ρ λ2 σ2

                  -> ({ eval (BIN op p1 p2) ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v },
                    Composable ρ λ' σ') @-}
labelProofBin :: (Fractional p, Eq p, Ord p)
              => Int -> Int -> Int -> Int -> DSL p -> DSL p -> BinOp p
              -> NameValuation p
              -> LabelEnv p Int -> LabelEnv p Int -> LabelEnv p Int
              -> M.Map Int p

              -> (String -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int -> LDSL p Int -> LDSL p Int
              -> M.Map Int p -> M.Map Int p -> M.Map Int p

              -> p -> p -> p

              -> Proof -> (String -> Proof)
              -> Proof -> (String -> Proof)

              -> (Proof, String -> Proof)
labelProofBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 v v1 v2 ih1 π1 ih2 π2 = case op of
  ADD           -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  SUB           -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  MUL           -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  LINCOMB k1 k2 -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  AND -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  OR  -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  XOR -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  UnsafeAND -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  UnsafeOR  -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
  UnsafeXOR -> ((), \x -> π2 x ? notElemLemma' x (outputWire e') λ2)
