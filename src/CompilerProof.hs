{-@ infix ! @-}
{-# OPTIONS -Wno-unused-matches -Wno-unused-imports
            -Wno-redundant-constraints #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module CompilerProof where

import Vec
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
                 -> σ:VecN p m
                 -> { coherent m pr σ <=>
                      satisfies (nGates pr) m σ (compile m pr) } @-}
compileProof :: (Eq p, Fractional p) => Int -> LProg p Int -> Vec p -> Proof
compileProof m (LExpr e) σ = compileProofE m e σ
compileProof m (LAss a) σ = compileProofA m a σ

{-@ compileProofE :: m:Nat
                  -> e:LDSL p (Btwn 0 m)
                  -> σ:VecN p m
                  -> { coherentE m e σ <=>
                       satisfies (nGatesE e) m σ (compileE m e) } @-}
compileProofE :: (Eq p, Fractional p) => Int -> LDSL p Int -> Vec p -> Proof
compileProofE m e σ = case e of
  LWIRE _ i -> trivial
  LVAR s τ i -> case τ of
    TF -> trivial
    TBool -> trivial
  LCONST x i -> trivial
  LDIV e1 e2 w i -> compileProofE m e1 σ ?
                    compileProofE m e2 σ ?
                    satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
    where n1 = nGatesE e1; n2 = nGatesE e2
  --FIXME: use or-patterns
  LUN op e1 i -> case op of
    ADDC _    -> compileProofE m e1 σ
    MULC _    -> compileProofE m e1 σ
    NOT       -> compileProofE m e1 σ
    UnsafeNOT -> compileProofE m e1 σ
  LBIN op e1 e2 i -> case op of
    ADD -> proof; SUB -> proof; MUL -> proof; LINCOMB _ _ -> proof
    AND -> proof; UnsafeAND -> proof;
    OR  -> proof; UnsafeOR  -> proof;
    XOR -> proof; UnsafeXOR -> proof;
    where proof = compileProofE m e1 σ ? compileProofE m e2 σ
                ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
          n1 = nGatesE e1; n2 = nGatesE e2

  LEQLC e1 k w i -> compileProofE m e1 σ


{-@ compileProofA :: m:Nat
                  -> a:LAss p (Btwn 0 m)
                  -> σ:VecN p m
                  -> { coherentA m a σ <=>
                       satisfies (nGatesA a) m σ (compileA m a) } @-}
compileProofA :: (Eq p, Fractional p) => Int -> LAss p Int -> Vec p -> Proof
compileProofA m a σ = case a of
  LNZERO e1 w -> compileProofE m e1 σ
  LBOOLEAN e1 -> compileProofE m e1 σ
  LEQA e1 e2  -> compileProofE m e1 σ ? compileProofE m e2 σ
               ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
    where n1 = nGatesE e1; n2 = nGatesE e2

{-@ satisfiesDistr :: n1:Nat -> n2:Nat -> m:Nat
                   -> σ:VecN p m
                   -> pr1:Circuit p n1 m -> pr2:Circuit p n2 m ->
                      { satisfies (n1+n2) m σ (append' pr1 pr2) <=>
                        satisfies n1 m σ pr1 && satisfies n2 m σ pr2 } @-}
satisfiesDistr :: Num p => Int -> Int -> Int ->
                  Vec p -> Circuit p -> Circuit p -> Proof
satisfiesDistr _  _  _ σ []      pr2 = trivial
satisfiesDistr n1 n2 m σ (p1:ps) pr2 = satisfiesDistr (n1-1) n2 m σ ps pr2

-- Some partial correctness results --------------------------------------------

-- The output of ‘isEqlCGate’ is always a boolean
{-@ isEqlCBoolean :: m:Nat -> a:Btwn 0 m -> w:Btwn 0 m -> c:Btwn 0 m -> k:p
                  -> σ:VecN p m
                  -> {satisfies 2 m σ (isEqlCGate m k (mkList3 a w c)) =>
                      boolean (σ!c)} @-}
isEqlCBoolean :: Num p => Int -> Int -> Int -> Int -> p -> Vec p -> Proof
isEqlCBoolean m a w c k σ = trivial

-- Unsafe boolean operations are safe (equivalent to the normal boolean
-- operations, and in particular not under-constrained) under the assumption
-- that their arguments are boolean

{-@ unsafeNotCorrect :: m:Nat -> a:Btwn 0 m -> c:Btwn 0 m
                     -> σ:VecN p m
                     -> { boolean (σ!a) &&
                           satisfies 1 m σ (unsafeNotGate m (mkList2 a c)) <=>
                          boolean (σ!a) &&
                           σ!c == if (σ!a == 1) then 0 else 1 } @-}
unsafeNotCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Vec p -> Proof
unsafeNotCorrect m a c σ = trivial

{-@ unsafeAndCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m
                     -> σ:VecN p m
                     -> { boolean (σ!a) && boolean (σ!b) &&
                           satisfies 1 m σ (unsafeAndGate m (mkList3 a b c)) <=>
                          boolean (σ!a) && boolean (σ!b) &&
                           σ!c == if (σ!a == 0 || σ!b == 0) then 0 else 1 } @-}
unsafeAndCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> Vec p -> Proof
unsafeAndCorrect m a b c σ = trivial

{-@ unsafeOrCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m
                    -> σ:VecN p m
                    -> { boolean (σ!a) && boolean (σ!b) &&
                          satisfies 1 m σ (unsafeOrGate m (mkList3 a b c)) <=>
                         boolean (σ!a) && boolean (σ!b) &&
                          σ!c == if (σ!a == 1 || σ!b == 1) then 1 else 0 } @-}
unsafeOrCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> Vec p -> Proof
unsafeOrCorrect m a b c σ = trivial

{-@ unsafeXorCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m
                     -> σ:VecN p m
                     -> { boolean (σ!a) && boolean (σ!b) &&
                           satisfies 1 m σ (unsafeXorGate m (mkList3 a b c)) <=>
                          boolean (σ!a) && boolean (σ!b) &&
                           σ!c == if (σ!a /= σ!b) then 1 else 0 } @-}
unsafeXorCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> Vec p -> Proof
unsafeXorCorrect m a b c σ = trivial
