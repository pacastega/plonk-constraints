{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module BooleanProof where

import Utils
import DSL
import Semantics

import Language.Haskell.Liquid.ProofCombinators

{-@ booleanProof :: ρ:NameValuation p
                 -> e:BoolDSL p
                 -> {v:DSLValue p | eval e ρ == Just v}
                 -> { v == VF 0 || v == VF 1 } @-}
booleanProof :: (Fractional p, Eq p)
             => NameValuation p -> DSL p -> DSLValue p -> Proof
booleanProof ρ e _ = case eval e ρ of Just _ -> trivial


-- workarounds to fix "crash: unknown constant"

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
