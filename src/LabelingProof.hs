{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--cores=1" @-}

module LabelingProof where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import Utils
import TypeAliases

import Vec
import DSL
import Label
import WitnessGeneration
import Semantics

import LabelingLemmas

import Language.Haskell.Liquid.ProofCombinators


{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0


-- ∀x ∈ dom(Λ) . ρ(x) = σ(Λ(x))
{-@ type Composable Ρ Λ Σ = var:{String | elem' var (M.keys Λ)}
                         -> {(M.lookup var Ρ = M.lookup (M.lookup' var Λ) Σ)} @-}


-- this corresponds to Lemma 2. from the paper
{-@ labelProof1 :: m0:Nat -> m:{Nat | m >= m0}
                -> e:{TypedDSL p | scalar e}
                -> ρ:NameValuation p
                -> λ:LabelEnv p (Btwn 0 m0)
                -> σ:M.Map (Btwn 0 m0) p

                -> Composable ρ λ σ

                -> λ':LabelEnv p (Btwn 0 m)
                -> e':{LDSL p (Btwn 0 m) | label' e m0 λ = (m, mkList1 e', λ')}
                -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ e' σ}

                -> v:p

                -> ({ eval e ρ = Just (VF v) <=>
                      M.lookup (outputWire e') σ' = Just v },
                    Composable ρ λ' σ') @-}
labelProof1 :: (Fractional p, Eq p, Ord p)
            => Int -> Int -> DSL p
            -> NameValuation p
            -> LabelEnv p Int
            -> M.Map Int p

            -> (String -> Proof)

            -> LabelEnv p Int
            -> LDSL p Int
            -> M.Map Int p

            -> p

            -> (Proof, String -> Proof)
labelProof1 m0 m e ρ λ σ π λ' e' σ' v = case e of
  VAR s τ -> case M.lookup s λ of
    Nothing -> case τ of
      TF -> (trivial,
             \x -> if x == s
                   then trivial
                   else elem' x (M.keys λ')
                     ?? freshLemma (outputWire e') λ ? π x ? M.lookup' x λ)
      TBool -> (trivial,
               \x -> if x == s
                     then trivial
                     else elem' x (M.keys λ')
                       ?? freshLemma (outputWire e') λ ? π x ? M.lookup' x λ)
    Just j  -> (elementLemma s j λ ? π s ? lookupLemma s λ, \x -> π x)
  CONST _ -> (trivial, \x -> π x ? notElemLemma' x (outputWire e') λ)

  BOOLEAN b -> case b of
    True -> (trivial, \x -> π x ? notElemLemma' x (outputWire e') λ)
    False -> (trivial, \x -> π x ? notElemLemma' x (outputWire e') λ)

  BIN op p1 p2 -> case op of
      DIV -> (ih1 ? ih2,
             \x -> let j = M.lookup' x λ2
                   in π2 x ? notElemLemma' x i λ2 ? notElemLemma' x w λ2
                           ? (M.lookup j σ'
                              === M.lookup j (M.insert i (v1/v2) σ2)
                              === M.lookup j σ2))
        where (m1, ps1, λ1) = label' p1 m0 λ
              (m2, ps2, λ2) = label' p2 m1 λ1
              (LDIV _ _ w i) = e'
              p1' = case ps1 of [x] -> x
              p2' = case ps2 of [x] -> x
              σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
              σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
              v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
              v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
              (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
              (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2

      EQL -> if v1 == v2
             then (ih1 ? ih2
                   ? liquidAssert (M.lookup (outputWire sub) σ3 == Just (v1 - v2))
                   ? (eval (BIN EQL p1 p2) ρ === Just (eqlFn (VF v1) (VF v2))),
                   \x -> let j = M.lookup' x λ2
                         in π2 x ? notElemLemma' x i λ2 ? notElemLemma' x w λ2
                                 ? (M.lookup j σ'
                                    === M.lookup j (M.insert w zero σ3)
                                    === M.lookup j σ3))
                  ? liquidAssert (σ' == M.insert i one (M.insert w zero σ3))
             else (ih1 ? ih2
                   ? liquidAssert (M.lookup (outputWire sub) σ3 == Just (v1 - v2))
                   ? (eval (BIN EQL p1 p2) ρ === Just (eqlFn (VF v1) (VF v2))),
                   \x -> let j = M.lookup' x λ2
                         in π2 x ? notElemLemma' x i λ2 ? notElemLemma' x w λ2
                                 ? (M.lookup j σ'
                                    === M.lookup j (M.insert w (1/(v1-v2)) σ3)
                                    === M.lookup j σ3))
                  ? liquidAssert (σ' == M.insert i zero (M.insert w (1/(v1-v2)) σ3))

        where (m1, ps1, λ1) = label' p1 m0 λ
              (m2, ps2, λ2) = label' p2 m1 λ1
              (m3, [sub], λ3) = label' (BIN SUB p1 p2) m0 λ
              (LEQLC _ _ w i) = e'
              p1' = case ps1 of [x] -> x
              p2' = case ps2 of [x] -> x
              σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
              σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
              σ3 = case update m3 ρ sub σ  ? updateLemma m3 m ρ sub σ  of Just s -> s
              v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
              v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
              (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
              (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2

      ADD ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (add (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

      SUB ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (sub (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

      MUL ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (mul (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

      LINCOMB k1 k2 ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (linCombFn k1 k2 (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

      AND ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (andFn (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

      OR  ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (orFn (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

      XOR ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (xorFn (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

      UnsafeAND ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (andFn (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

      UnsafeOR  ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (orFn (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

      UnsafeXOR ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (m2, ps2, λ2) = label' p2 m1 λ1
            p1' = case ps1 of [x] -> x
            p2' = case ps2 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ  of Just s -> s
            σ2 = case update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1 of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            v2 = case M.lookup (outputWire p2') σ2 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 v1
            (ih2, π2) = labelProof1 m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 v2
        in (ih1 ? ih2
            ? (eval (BIN op p1 p2) ρ === Just (xorFn (VF v1) (VF v2))),
           \x -> π2 x ? notElemLemma' x (outputWire e') λ2)

  UN op p1 -> case op of

      ADDC _ ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
        in (ih1, \x -> π1 x ? notElemLemma' x (outputWire e') λ1)

      MULC _ ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
        in (ih1, \x -> π1 x ? notElemLemma' x (outputWire e') λ1)

      NOT ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
        in (ih1, \x -> π1 x ? notElemLemma' x (outputWire e') λ1)

      UnsafeNOT ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
        in (ih1, \x -> π1 x ? notElemLemma' x (outputWire e') λ1)

      ISZERO ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (LEQLC _ _ w i) = e'
            p1' = case ps1 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
        in if v1 == 0
           then (ih1,
                \x -> let j = M.lookup' x λ1
                      in π1 x ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                              ? (M.lookup j σ'
                                 === M.lookup j (M.insert w zero σ1)
                                 === M.lookup j σ1))
                ? liquidAssert (σ' == M.insert i one (M.insert w zero σ1))
           else (ih1,
                \x -> let j = M.lookup' x λ1
                      in π1 x ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                              ? (M.lookup j σ'
                                 === M.lookup j (M.insert w (1/v1) σ1)
                                 === M.lookup j σ1))
                ? liquidAssert (σ' == M.insert i zero (M.insert w (1/v1) σ1))

      EQLC k ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            (LEQLC _ _ w i) = e'
            p1' = case ps1 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
        in if v1 == k
           then (ih1,
                \x -> let j = M.lookup' x λ1
                      in π1 x ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                              ? (M.lookup j σ'
                                 === M.lookup j (M.insert w 0 σ1)
                                 === M.lookup j σ1))
                ? liquidAssert (σ' == M.insert i one (M.insert w zero σ1))
           else (ih1,
                \x -> let j = M.lookup' x λ1
                      in π1 x ? notElemLemma' x i λ1 ? notElemLemma' x w λ1
                              ? (M.lookup j σ'
                                 === M.lookup j (M.insert w (1/(v1-k)) σ1)
                                 === M.lookup j σ1))
                ? liquidAssert (σ' == M.insert i zero (M.insert w (1/(v1-k)) σ1))

      BoolToF ->
        let (m1, ps1, λ1) = label' p1 m0 λ
            p1' = case ps1 of [x] -> x
            σ1 = case update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ of Just s -> s
            v1 = case M.lookup (outputWire p1') σ1 of Just v -> v
            (ih1, π1) = labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
        in case M.lookup (outputWire p1') σ1 of
          Just v1 -> labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1
          Nothing -> case eval p1 ρ of
            Just (VF v1') -> labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 v1'
            Nothing -> labelProof1 m0 m1 p1 ρ λ  σ  π λ1 p1' σ1 0


{-
-- This is Theorem 2.
{-@ labelProof :: m':Nat -> m:{Nat | m >= m'}
               -> e:{TypedDSL p | scalar e}
               -> as:Store p
               -> ρ:NameValuation p
               -> λ:LabelEnv p (Btwn 0 m) -> λ':LabelEnv p (Btwn 0 m)
               -> {as':[LDSL p (Btwn 0 m)] |
                       labelStore as 0 M.MTip = (m', as', λ')}
               -> {es':[LDSL p (Btwn 0 m)] |
                       label' e m' λ' = (m, es', λ)}
               -> σ:{VecN p m | σ = witnessGen m as' ρ}
               -> {assertionsHold ρ as <=> semanticsHold m σ as'} @-}
labelProof :: (Fractional p, Eq p) => Int -> Int -> DSL p -> Store p
           -> NameValuation p
           -> LabelEnv p Int -> LabelEnv p Int
           -> [LDSL p Int] -> [LDSL p Int]
           -> Vec p
           -> Proof
labelProof m' m e []     ρ λ λ' as' es' σ = trivial
labelProof m' m e (a:as) ρ λ λ' as' es' σ = case a of
  DEF _ _ _ -> undefined -- dummy
  NZERO p1  -> undefined -- IH missing
  BOOL p1   -> undefined -- IH missing
  EQA p1 p2 -> undefined -- IH missing
-}
