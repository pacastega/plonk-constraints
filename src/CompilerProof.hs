{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ infix ! @-}
{-# OPTIONS -Wno-unused-matches -Wno-unused-imports
            -Wno-redundant-constraints #-}
{-# LANGUAGE FlexibleContexts #-}
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


{-@ satisfiesDistr :: n1:Nat -> n2:Nat -> m:Nat ->
                      input:VecN p m ->
                      c1:Circuit p n1 m -> c2:Circuit p n2 m ->
                      {satisfies (n1+n2) m input (append' c1 c2) <=>
                       satisfies n1 m input c1 && satisfies n2 m input c2} @-}
satisfiesDistr :: Num p => Int -> Int -> Int ->
                  Vec p -> Circuit p -> Circuit p -> Proof
satisfiesDistr _  _  _ input []     c2 = trivial
satisfiesDistr n1 n2 m input (c:cs) c2 = satisfiesDistr (n1-1) n2 m input cs c2
