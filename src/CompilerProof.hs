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

import ArithmeticGates
import LogicGates

import DSL

import Language.Haskell.Liquid.ProofCombinators

{-@ compileProof :: m:Nat ->
                    program:LDSL p (Btwn 0 m) ->
                    input:VecN p m ->
                    {semanticsAreCorrect m program input <=>
                     satisfies (nGates program) m input (compile m program)} @-}
compileProof :: (Eq p, Fractional p) => Int -> LDSL p Int -> Vec p -> Proof
compileProof m (LWIRE i)      input = trivial
compileProof m (LVAR s i)     input = trivial
compileProof m (LCONST x i)   input = trivial
compileProof m (LADD p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2)
compileProof m (LSUB p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2)
compileProof m (LMUL p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2)
compileProof m (LDIV p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2)
compileProof m (LISZERO p1 w i) input = compileProof m p1 input
compileProof m (LEQLC p1 k w i) input = compileProof m p1 input
compileProof m (LNOT p1 i) input = compileProof m p1 input ?
                                   semanticsAreCorrect m (LNOT p1 i) input
compileProof m (LAND p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2) ?
     semanticsAreCorrect m (LAND p1 p2 i) input
compileProof m (LOR p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2) ?
     semanticsAreCorrect m (LOR p1 p2 i) input
compileProof m (LXOR p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2) ?
     semanticsAreCorrect m (LXOR p1 p2 i) input
compileProof m (LUnsafeNOT p1 i) input =
  compileProof m p1 input ?
  semanticsAreCorrect m (LUnsafeNOT p1 i) input
compileProof m (LUnsafeAND p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2) ?
     semanticsAreCorrect m (LUnsafeAND p1 p2 i) input
compileProof m (LUnsafeOR p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2) ?
     semanticsAreCorrect m (LUnsafeOR p1 p2 i) input
compileProof m (LUnsafeXOR p1 p2 i) input =
  let n1 = nGates p1
      n2 = nGates p2
  in compileProof m p1 input ?
     compileProof m p2 input ?
     satisfiesDistr n1 n2 m input (compile m p1) (compile m p2) ?
     semanticsAreCorrect m (LUnsafeXOR p1 p2 i) input


{-@ satisfiesDistr :: n1:Nat -> n2:Nat -> m:Nat ->
                      input:VecN p m ->
                      c1:Circuit p n1 m -> c2:Circuit p n2 m ->
                      {satisfies (n1+n2) m input (append' c1 c2) <=>
                       satisfies n1 m input c1 && satisfies n2 m input c2} @-}
satisfiesDistr :: Num p => Int -> Int -> Int ->
                  Vec p -> Circuit p -> Circuit p -> Proof
satisfiesDistr _  _  _ input []     c2 = trivial
satisfiesDistr n1 n2 m input (c:cs) c2 = satisfiesDistr (n1-1) n2 m input cs c2

-- Some partial correctness results --------------------------------------------

-- The output of ‘isZeroGate’ is always a boolean
{-@ isZeroBoolean :: m:Nat -> a:Btwn 0 m -> w:Btwn 0 m -> c:Btwn 0 m ->
                     input:VecN p m ->
                     {satisfies 2 m input (isZeroGate m (mkList3 a w c)) =>
                      boolean (input!c)} @-}
isZeroBoolean :: Num p => Int -> Int -> Int -> Int -> Vec p -> Proof
isZeroBoolean m a w c input = trivial

-- The output of ‘isEqlCGate’ is always a boolean
{-@ isEqlCBoolean :: m:Nat -> a:Btwn 0 m -> w:Btwn 0 m -> c:Btwn 0 m -> k:p ->
                     input:VecN p m ->
                     {satisfies 2 m input (isEqlCGate m k (mkList3 a w c)) =>
                      boolean (input!c)} @-}
isEqlCBoolean :: Num p => Int -> Int -> Int -> Int -> p -> Vec p -> Proof
isEqlCBoolean m a w c k input = trivial

-- Unsafe boolean operations are safe (equivalent to the normal boolean
-- operations, and in particular not under-constrained) under the assumption
-- that their arguments are boolean

{-@ unsafeNotCorrect :: m:Nat -> a:Btwn 0 m -> c:Btwn 0 m ->
        input:VecN p m ->
        {boolean (input!a) &&
          satisfies 1 m input (unsafeNotGate m (mkList2 a c)) <=>
         boolean (input!a) &&
          input!c == if (input!a == 1) then 0 else 1} @-}
unsafeNotCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Vec p -> Proof
unsafeNotCorrect m a c input = trivial

{-@ unsafeAndCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m ->
        input:VecN p m ->
        {boolean (input!a) && boolean (input!b) &&
          satisfies 1 m input (unsafeAndGate m (mkList3 a b c)) <=>
         boolean (input!a) && boolean (input!b) &&
          input!c == if (input!a == 0 || input!b == 0) then 0 else 1} @-}
unsafeAndCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> Vec p -> Proof
unsafeAndCorrect m a b c input = trivial

{-@ unsafeOrCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m ->
        input:VecN p m ->
        {boolean (input!a) && boolean (input!b) &&
          satisfies 1 m input (unsafeOrGate m (mkList3 a b c)) <=>
         boolean (input!a) && boolean (input!b) &&
          input!c == if (input!a == 1 || input!b == 1) then 1 else 0} @-}
unsafeOrCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> Vec p -> Proof
unsafeOrCorrect m a b c input = trivial

{-@ unsafeXorCorrect :: m:Nat -> a:Btwn 0 m -> b:Btwn 0 m -> c:Btwn 0 m ->
        input:VecN p m ->
        {boolean (input!a) && boolean (input!b) &&
          satisfies 1 m input (unsafeXorGate m (mkList3 a b c)) <=>
         boolean (input!a) && boolean (input!b) &&
          input!c == if (input!a /= input!b) then 1 else 0} @-}
unsafeXorCorrect :: (Eq p, Num p) => Int -> Int -> Int -> Int -> Vec p -> Proof
unsafeXorCorrect m a b c input = trivial
