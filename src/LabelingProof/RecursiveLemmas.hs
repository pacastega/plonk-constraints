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

{-@ wellTypedUn :: e1:DSL p -> op:{UnOp p | wellTyped (UN op e1)}
                -> { wellTyped e1 } @-}
wellTypedUn :: DSL p -> UnOp p -> Proof
wellTypedUn e1 op = trivial


{-@ wellTypedBin :: e1:DSL p -> e2:DSL p
                 -> op:{BinOp p | wellTyped (BIN op e1 e2)}
                 -> { wellTyped e1 && wellTyped e2 } @-}
wellTypedBin :: DSL p -> DSL p -> BinOp p -> Proof
wellTypedBin e1 e2 op = trivial


-- workarounds to fix "crash: unknown constant"

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
