{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module LabelingProof.RecursiveLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import TypeAliases
import DSL
import Utils
import WitnessGeneration
import Label

import WitnessGenProof.WitnessGenLemmas

import Language.Haskell.Liquid.ProofCombinators

-- well-typedness is propagated to the arguments -------------------------------

{-@ wellTypedUn :: e1:DSL p -> op:{UnOp p | wellTyped (UN op e1)}
                -> { wellTyped e1 } @-}
wellTypedUn :: DSL p -> UnOp p -> Proof
wellTypedUn e1 op = trivial


{-@ wellTypedBin :: e1:DSL p -> e2:DSL p
                 -> op:{BinOp p | wellTyped (BIN op e1 e2)}
                 -> { wellTyped e1 && wellTyped e2 } @-}
wellTypedBin :: DSL p -> DSL p -> BinOp p -> Proof
wellTypedBin e1 e2 op = trivial


{-@ wellTypedCons :: e1:DSL p -> e2:{DSL p | wellTyped (CONS e1 e2)}
                  -> { wellTyped e1 && wellTyped e2 } @-}
wellTypedCons :: DSL p -> DSL p -> Proof
wellTypedCons e1 e2 = trivial


-- subexpressions are smaller --------------------------------------------------

{-@ sizeUn :: e1:DSL p -> op:UnOp p -> { size e1 < size (UN op e1) } @-}
sizeUn :: DSL p -> UnOp p -> Proof
sizeUn e1 op = trivial


{-@ sizeBin :: e1:DSL p -> e2:DSL p -> op:BinOp p
            -> { size e1 < size (BIN op e1 e2) &&
                 size e2 < size (BIN op e1 e2) } @-}
sizeBin :: DSL p -> DSL p -> BinOp p -> Proof
sizeBin e1 e2 op = trivial


{-@ sizeCons :: e1:DSL p -> e2:DSL p
             -> { size e1 < size (CONS e1 e2) &&
                  size e2 < size (CONS e1 e2) } @-}
sizeCons :: DSL p -> DSL p -> Proof
sizeCons e1 e2 = trivial


-- workarounds to fix "crash: unknown constant"

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
