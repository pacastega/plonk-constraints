{-# OPTIONS -Wno-unused-matches #-}
{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module CompilerProof where

import Vec
import Constraints
import Circuits
import Utils -- needed for the reflection

import GHC.TypeNats (KnownNat)

import DSL

import Language.Haskell.Liquid.ProofCombinators

{-@ compileProof :: m:{v:Int | v >= 3} ->
                    program:LDSL p (Btwn Int 0 m) ->
                    input:VecN (F p) m ->
                    {semanticsAreCorrect m program input <=>
                     satisfies (nGates program) m input (compile m program)} @-}
compileProof :: KnownNat p =>
                Int -> LDSL p Int -> Vec (F p) -> Proof
compileProof m (LWIRE i) input
  =   semanticsAreCorrect m (LWIRE i) input
  === True
  === satisfies 0 m input (emptyCircuit m)
  *** QED
compileProof m (LCONST x i) input
  =   semanticsAreCorrect m (LCONST x i) input
  === input!i == x
  === satisfies 1 m input (constGate m x i)
  *** QED
compileProof m (LADD p1 p2 i) input = undefined
compileProof m (LMUL p1 p2 i) input = undefined
