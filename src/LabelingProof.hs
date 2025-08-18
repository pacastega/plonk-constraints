{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

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

import Language.Haskell.Liquid.ProofCombinators

{-@ updateLemma :: m:Nat -> m':{Nat | m' >= m}
                -> ρ:NameValuation p -> e:LDSL p (Btwn 0 m)
                -> σ:M.Map (Btwn 0 m) p
                -> { update m ρ e σ == update m' ρ e σ } @-}
updateLemma :: (Eq p, Fractional p) => Int -> Int
                   -> NameValuation p -> LDSL p Int -> M.Map Int p -> Proof
updateLemma m m' ρ e σ = case e of
  LWIRE _ -> ()
  LVAR {} -> ()
  LCONST {} -> ()

  LADD e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LSUB e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LMUL e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LDIV e1 e2 _ _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LADDC e1 _ _ -> updateLemma m m' ρ e1 σ
  LMULC e1 _ _ -> updateLemma m m' ρ e1 σ
  LLINCOMB _ e1 _ e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LNOT e1 _ -> updateLemma m m' ρ e1 σ
  LAND e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LOR  e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LXOR e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LUnsafeNOT e1 _ -> updateLemma m m' ρ e1 σ
  LUnsafeAND e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LUnsafeOR  e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1
  LUnsafeXOR e1 e2 _ -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1

  LEQLC e1 _ _ _ -> updateLemma m m' ρ e1 σ
  LNZERO e1 _    -> updateLemma m m' ρ e1 σ

  LNZERO e1 _ -> updateLemma m m' ρ e1 σ
  LBOOL e1    -> updateLemma m m' ρ e1 σ
  LEQA e1 e2  -> updateLemma m m' ρ e1 σ ? case update m ρ e1 σ of
    Nothing -> (); Just σ1 -> updateLemma m m' ρ e2 σ1


{-@ reflect ? @-}


-- this corresponds to Lemma 2. from the paper
{-@ labelProof1 :: m0:Nat -> m:{Nat | m >= m0}
                -> e:{TypedDSL p | scalar e}
                -> ρ:NameValuation p
                -> λ:LabelEnv p (Btwn 0 m0)
                -> σ:M.Map (Btwn 0 m0) p

                -> λ':LabelEnv p (Btwn 0 m)
                -> e':{LDSL p (Btwn 0 m) | label' e m0 λ = (m, mkList1 e', λ')}
                -> σ':{M.Map (Btwn 0 m) p | Just σ' = update m ρ e' σ}

                -> v:p

                -> { eval e ρ = Just (VF v) <=>
                     M.lookup (outputWire e') σ' = Just v } @-}
labelProof1 :: (Fractional p, Eq p, Ord p)
            => Int -> Int -> DSL p
            -> NameValuation p
            -> LabelEnv p Int
            -> M.Map Int p

            -> LabelEnv p Int
            -> LDSL p Int
            -> M.Map Int p

            -> p

            -> (Proof)
labelProof1 m0 m e ρ λ σ λ' e' σ' v = case e of
  VAR _ _ -> undefined
  CONST _ -> trivial

  BOOLEAN b -> case b of True -> trivial; False -> trivial

  ADD p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2
  SUB p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2
  MUL p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2
  DIV p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2

  ADDC p1 _ ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
       Just v1 -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
  MULC p1 _ ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
       Just v1 -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
  LINCOMB _ p1 _ p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2

  NOT p1 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
       Just v1 -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
  AND p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2
  OR p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2
  XOR p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2

  UnsafeNOT p1 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
       Just v1 -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
  UnsafeAND p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2
  UnsafeOR p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2
  UnsafeXOR p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
                           ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2

  ISZERO p1 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (LEQLC _ _ w i) = e'
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
       Just v1 -> if v1 == 0
         then labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
            ? liquidAssert (σ' == M.insert i one (M.insert w zero σ1))
         else labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
            ? liquidAssert (σ' == M.insert i zero (M.insert w (1/v1) σ1))

  EQL p1 p2 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (m2, [p2'], λ2) = label' p2 m1 λ1
        (m3, [sub], λ3) = label' (SUB p1 p2) m0 λ
        (LEQLC _ _ w i) = e'
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
        Just σ2 = update m2 ρ p2' σ1 ? updateLemma m2 m ρ p2' σ1
        Just σ3 = update m3 ρ sub σ  ? updateLemma m3 m ρ sub σ
    in case (M.lookup (outputWire p1') σ1, M.lookup (outputWire p2') σ2) of
       (Just v1, Just v2) -> if v1 == v2
         then labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
            ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2
            ? liquidAssert (M.lookup (outputWire sub) σ3 == Just (v1 - v2))
            ? liquidAssert (σ' == M.insert i one (M.insert w zero σ3))
         else labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
            ? labelProof1 m1 m2 p2 ρ λ1 σ1 λ2 p2' σ2 v2
            ? liquidAssert (M.lookup (outputWire sub) σ3 == Just (v1 - v2))
            ? liquidAssert (σ' == M.insert i zero (M.insert w (1/(v1-v2)) σ3))

  EQLC p1 k ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        (LEQLC _ _ w i) = e'
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
       Just v1 -> if v1 == k
         then labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
            ? liquidAssert (σ' == M.insert i one (M.insert w zero σ1))
         else labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
            ? liquidAssert (σ' == M.insert i zero (M.insert w (1/(v1-k)) σ1))

  NIL _ -> error "vectors are not scalar"
  CONS h ts -> error "vectors are not scalar"

  BoolToF p1 ->
    let (m1, [p1'], λ1) = label' p1 m0 λ
        Just σ1 = update m1 ρ p1' σ  ? updateLemma m1 m ρ p1' σ
    in case M.lookup (outputWire p1') σ1 of
       Just v1 -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1
       Nothing -> case eval p1 ρ of
         Just (VF v1') -> labelProof1 m0 m1 p1 ρ λ  σ  λ1 p1' σ1 v1'
         Nothing -> ()

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
