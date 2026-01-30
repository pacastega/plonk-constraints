{-# LANGUAGE CPP #-}
{-@ infix ! @-}
{-# OPTIONS -Wno-unused-matches -Wno-unused-imports
            -Wno-redundant-constraints #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module CompilerProof where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import Constraints
import Circuits
import Utils
import TypeAliases

import ArithmeticGates
import LogicGates

import DSL

import Language.Haskell.Liquid.ProofCombinators

-- This is Theorem 1 from the paper
{-@ compileProof :: m:Nat
                 -> pr:LProg p (Btwn 0 m)
                 -> {σ:WireValuation p m | closedProg m σ pr}
                 -> { coherent m pr σ <=>
                      satisfies (nGates pr) m σ (compile m pr) } @-}
compileProof :: (Eq p, Fractional p)
             => Int -> LProg p Int -> WireValuation p -> Proof
compileProof m (LExpr e) σ = compileProofE m e σ
compileProof m (LAss a) σ = compileProofA m a σ

{-@ compileProofE :: m:Nat
                  -> e:LDSL p (Btwn 0 m)
                  -> {σ:WireValuation p m | closedExpr m σ e}
                  -> { coherentE m e σ <=>
                       satisfies (nGatesE e) m σ (compileE m e) } @-}
compileProofE :: (Eq p, Fractional p)
              => Int -> LDSL p Int -> WireValuation p -> Proof
compileProofE m e σ = case e of
  LWIRE _ i -> trivial
  LVAR s τ i -> case τ of
    TF -> trivial
    TBool -> trivial
  LCONST x i -> trivial
  LDIV e1 e2 w i -> compileProofE m e1 σ ? compileProofE m e2 σ
                  ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
                  ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
                  ? closedExpr m σ e2 ?? M.lookup' (outputWire e2) σ
    where n1 = nGatesE e1; n2 = nGatesE e2

  LUN op e1 i -> case op of
    ADDC _    -> proof
    MULC _    -> proof
    NOT       -> proof
    UnsafeNOT -> proof
    where proof = compileProofE m e1 σ
                ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
  LBIN op e1 e2 i -> case op of
    ADD -> proof; SUB -> proof; MUL -> proof; LINCOMB _ _ -> proof;
    AND -> proof; UnsafeAND -> proof;
    OR  -> proof; UnsafeOR  -> proof;
    XOR -> proof; UnsafeXOR -> proof;
    where proof = compileProofE m e1 σ ? compileProofE m e2 σ
                ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
                ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
                ? closedExpr m σ e2 ?? M.lookup' (outputWire e2) σ
          n1 = nGatesE e1; n2 = nGatesE e2

  LEQLC e1 k w i -> compileProofE m e1 σ
                  ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ


{-@ compileProofA :: m:Nat
                  -> a:LAss p (Btwn 0 m)
                  -> {σ:WireValuation p m | closedAssertion m σ a}
                  -> { coherentA m a σ <=>
                       satisfies (nGatesA a) m σ (compileA m a) } @-}
compileProofA :: (Eq p, Fractional p)
              => Int -> LAss p Int -> WireValuation p -> Proof
compileProofA m a σ = case a of
  LNZERO e1 w -> compileProofE m e1 σ
               ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
  LBOOLEAN e1 -> compileProofE m e1 σ
               ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
  LEQA e1 e2  -> compileProofE m e1 σ ? compileProofE m e2 σ
               ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
               ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
               ? closedExpr m σ e2 ?? M.lookup' (outputWire e2) σ
    where n1 = nGatesE e1; n2 = nGatesE e2

{-@ satisfiesDistr :: n1:Nat -> n2:Nat -> m:Nat
                   -> σ:WireValuation p m
                   -> pr1:Circuit p n1 m -> pr2:Circuit p n2 m
                   -> { satisfies (n1+n2) m σ (append' pr1 pr2) <=>
                        satisfies n1 m σ pr1 && satisfies n2 m σ pr2 } @-}
satisfiesDistr :: Num p => Int -> Int -> Int ->
                  WireValuation p -> Circuit p -> Circuit p -> Proof
satisfiesDistr _  _  _ σ []      pr2 = trivial
satisfiesDistr n1 n2 m σ (p1:ps) pr2 = satisfiesDistr (n1-1) n2 m σ ps pr2

-- Some partial correctness results --------------------------------------------

-- The output of ‘isEqlCGate’ is always a boolean
{-@ isEqlCBoolean :: m:Nat -> a:Btwn 0 m -> w:Btwn 0 m -> c:Btwn 0 m -> k:p
                  -> {σ:WireValuation p m |
                                 M.member a σ && M.member w σ && M.member c σ}
                  -> TRUE @-}
isEqlCBoolean :: (Eq p, Num p) => Int -> Int -> Int -> Int -> p -> WireValuation p -> Bool
isEqlCBoolean m a w c k σ =
  if satisfies 2 m σ (isEqlCGate m k [a,w,c])
  then boolean (M.lookup' c σ)
  else True

-- Unsafe boolean operations are safe (equivalent to the normal boolean
-- operations, and in particular not under-constrained) under the assumption
-- that their arguments are boolean

{-@ unsafeNotCorrect :: m:Nat -> a:Btwn 0 m -> c:Btwn 0 m
                     -> {σ:WireValuation p m | M.member a σ && M.member c σ}
                     -> TRUE @-}
unsafeNotCorrect :: (Eq p, Num p) => Int -> Int -> Int -> WireValuation p -> Bool
unsafeNotCorrect m a c σ =
  (boolean va && satisfies 1 m σ (unsafeNotGate m [a,c])) ==
  (boolean va && vc == if (va == 1) then 0 else 1)
    where va = M.lookup' a σ; vc = M.lookup' c σ

{-@ unsafeAndCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m
                     -> {σ:WireValuation p m |
                                 M.member a σ && M.member b σ && M.member c σ}
                     -> TRUE @-}
unsafeAndCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> WireValuation p -> Bool
unsafeAndCorrect m a b c σ =
  (boolean va && boolean vb
       && satisfies 1 m σ (unsafeAndGate m [a,b,c])) ==
  (boolean va && boolean vb
       && vc == if (va == 0 || vb == 0) then 0 else 1)
    where va = M.lookup' a σ; vb = M.lookup' b σ; vc = M.lookup' c σ

{-@ unsafeOrCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m
                    -> {σ:WireValuation p m |
                                 M.member a σ && M.member b σ && M.member c σ}
                    -> TRUE @-}
unsafeOrCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> WireValuation p -> Bool
unsafeOrCorrect m a b c σ =
   (boolean va && boolean vb
        && satisfies 1 m σ (unsafeOrGate m [a,b,c])) ==
   (boolean va && boolean vb
        && vc == if (va == 1 || vb == 1) then 1 else 0)
    where va = M.lookup' a σ; vb = M.lookup' b σ; vc = M.lookup' c σ

{-@ unsafeXorCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m
                     -> {σ:WireValuation p m |
                                 M.member a σ && M.member b σ && M.member c σ}
                     -> TRUE @-}
unsafeXorCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> WireValuation p -> Bool
unsafeXorCorrect m a b c σ =
   (boolean va && boolean vb
        && satisfies 1 m σ (unsafeXorGate m [a,b,c])) ==
   (boolean va && boolean vb
        && vc == if (va /= vb) then 1 else 0)
    where va = M.lookup' a σ; vb = M.lookup' b σ; vc = M.lookup' c σ
