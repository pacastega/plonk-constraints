{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module CompilerProof where

import Vec
import Constraints
import ArithmeticGates
import Circuits
import Utils

import GHC.TypeNats (KnownNat)
import Data.FiniteField.PrimeField (PrimeField)
import PrimitiveRoot

import DSL

import Language.Haskell.Liquid.ProofCombinators

{-@ compileProof :: m:Nat1 ->
                    program:LDSL p (Btwn Int 0 m) ->
                    input:VecN (F p) m ->
                    {semanticsAreCorrect m program input <=>
                     satisfies (nGates program) m input (compile m program)} @-}
compileProof :: (KnownNat p, PrimitiveRoot (F p)) =>
                Int -> LDSL p Int -> Vec (F p) -> Proof
compileProof m (LWIRE i) input
  =   semanticsAreCorrect m (LWIRE i) input
  === True
  === satisfies 0 m input (emptyCircuit m)
  === satisfies 0 m input (fst' $ compile' m (LWIRE i))
  === satisfies 0 m input (compile m (LWIRE i))
  *** QED
compileProof m (LCONST x i)   input = undefined
compileProof m (LADD p1 p2 i) input = undefined
compileProof m (LMUL p1 p2 i) input = undefined
