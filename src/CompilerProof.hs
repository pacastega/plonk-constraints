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
{-@ compileProof :: m:Nat ->
                    program:LDSL p (Btwn 0 m) ->
                    σ:VecN p m ->
                    {semanticsAreCorrect m program σ <=>
                     satisfies (nGates program) m σ (compile m program)} @-}
compileProof :: (Eq p, Fractional p) => Int -> LDSL p Int -> Vec p -> Proof
compileProof m (LWIRE _ i)    σ = trivial
compileProof m (LVAR s τ i)   σ = case τ of
  TF -> trivial
  TBool -> trivial
compileProof m (LCONST x i)   σ = trivial
compileProof m (LDIV p1 p2 w i) σ =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 σ ?
     compileProof m p2 σ ?
     satisfiesDistr n1 n2 m σ (compile m p1) (compile m p2)

compileProof m (LUN op p1 i)  σ = case op of
  ADDC _    -> compileProof m p1 σ
  MULC _    -> compileProof m p1 σ
  NOT       -> compileProof m p1 σ
  UnsafeNOT -> compileProof m p1 σ

compileProof m (LBIN op p1 p2 i) σ = case op of
  ADD -> proof; SUB -> proof; MUL -> proof; LINCOMB _ _ -> proof
  AND -> proof; UnsafeAND -> proof;
  OR  -> proof; UnsafeOR  -> proof;
  XOR -> proof; UnsafeXOR -> proof;
  where proof = compileProof m p1 σ -- IH 1
              ? compileProof m p2 σ -- IH 2
              ? satisfiesDistr n1 n2 m σ (compile m p1) (compile m p2)
        n1 = nGates p1; n2 = nGates p2

compileProof m (LEQLC p1 k w i) σ = compileProof m p1 σ

compileProof m (LNZERO p1 w) σ = compileProof m p1 σ
compileProof m (LBOOLEAN p1) σ = compileProof m p1 σ
compileProof m (LEQA p1 p2)  σ =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 σ ?
     compileProof m p2 σ ?
     satisfiesDistr n1 n2 m σ (compile m p1) (compile m p2)


{-@ satisfiesDistr :: n1:Nat -> n2:Nat -> m:Nat ->
                      σ:VecN p m ->
                      c1:Circuit p n1 m -> c2:Circuit p n2 m ->
                      {satisfies (n1+n2) m σ (append' c1 c2) <=>
                       satisfies n1 m σ c1 && satisfies n2 m σ c2} @-}
satisfiesDistr :: Num p => Int -> Int -> Int ->
                  Vec p -> Circuit p -> Circuit p -> Proof
satisfiesDistr _  _  _ σ []     c2 = trivial
satisfiesDistr n1 n2 m σ (c:cs) c2 = satisfiesDistr (n1-1) n2 m σ cs c2

-- Some partial correctness results --------------------------------------------

-- The output of ‘isEqlCGate’ is always a boolean
{-@ isEqlCBoolean :: m:Nat -> a:Btwn 0 m -> w:Btwn 0 m -> c:Btwn 0 m -> k:p ->
                     σ:VecN p m ->
                     {satisfies 2 m σ (isEqlCGate m k (mkList3 a w c)) =>
                      boolean (σ!c)} @-}
isEqlCBoolean :: Num p => Int -> Int -> Int -> Int -> p -> Vec p -> Proof
isEqlCBoolean m a w c k σ = trivial

-- Unsafe boolean operations are safe (equivalent to the normal boolean
-- operations, and in particular not under-constrained) under the assumption
-- that their arguments are boolean

{-@ unsafeNotCorrect :: m:Nat -> a:Btwn 0 m -> c:Btwn 0 m ->
        σ:VecN p m ->
        {boolean (σ!a) &&
          satisfies 1 m σ (unsafeNotGate m (mkList2 a c)) <=>
         boolean (σ!a) &&
          σ!c == if (σ!a == 1) then 0 else 1} @-}
unsafeNotCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Vec p -> Proof
unsafeNotCorrect m a c σ = trivial

{-@ unsafeAndCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m ->
        σ:VecN p m ->
        {boolean (σ!a) && boolean (σ!b) &&
          satisfies 1 m σ (unsafeAndGate m (mkList3 a b c)) <=>
         boolean (σ!a) && boolean (σ!b) &&
          σ!c == if (σ!a == 0 || σ!b == 0) then 0 else 1} @-}
unsafeAndCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> Vec p -> Proof
unsafeAndCorrect m a b c σ = trivial

{-@ unsafeOrCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m ->
        σ:VecN p m ->
        {boolean (σ!a) && boolean (σ!b) &&
          satisfies 1 m σ (unsafeOrGate m (mkList3 a b c)) <=>
         boolean (σ!a) && boolean (σ!b) &&
          σ!c == if (σ!a == 1 || σ!b == 1) then 1 else 0} @-}
unsafeOrCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> Vec p -> Proof
unsafeOrCorrect m a b c σ = trivial

{-@ unsafeXorCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m ->
        σ:VecN p m ->
        {boolean (σ!a) && boolean (σ!b) &&
          satisfies 1 m σ (unsafeXorGate m (mkList3 a b c)) <=>
         boolean (σ!a) && boolean (σ!b) &&
          σ!c == if (σ!a /= σ!b) then 1 else 0} @-}
unsafeXorCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> Vec p -> Proof
unsafeXorCorrect m a b c σ = trivial
