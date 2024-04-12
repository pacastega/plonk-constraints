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

import GHC.TypeNats (KnownNat)
import PrimitiveRoot
import ArithmeticGates

import DSL

import Language.Haskell.Liquid.ProofCombinators

{-@ compileProof :: m:{v:Int | v >= 3} ->
                    program:LDSL p (Btwn Int 0 m) ->
                    input:VecN (F p) m ->
                    {semanticsAreCorrect m program input <=>
                     satisfies (nGates program) m input (compile m program)} @-}
compileProof :: (KnownNat p, PrimitiveRoot (F p)) =>
                Int -> LDSL p Int -> Vec (F p) -> Proof
compileProof m (LWIRE i)      input = trivial
compileProof m (LCONST x i)   input = trivial
compileProof m (LADD p1 p2 i) input =
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


{-@ satisfiesDistr :: n1:Nat -> n2:Nat -> m:Nat ->
                      input:VecN (F p) m ->
                      c1:Circuit (F p) n1 m -> c2:Circuit (F p) n2 m ->
                      {satisfies (n1+n2) m input (append' c1 c2) <=>
                       satisfies n1 m input c1 && satisfies n2 m input c2} @-}
satisfiesDistr :: Int -> Int -> Int ->
                  Vec (F p) -> Circuit (F p) -> Circuit (F p) -> Proof
satisfiesDistr _  _  _ input []     c2 = trivial
satisfiesDistr n1 n2 m input (c:cs) c2 = satisfiesDistr (n1-1) n2 m input cs c2
