{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module BooleanProof where

import TypeAliases
import Utils
import DSL
import Semantics

import qualified Liquid.Data.Map as M

import Language.Haskell.Liquid.ProofCombinators

{-@ booleanProof :: ρ:NameValuation p
                 -> e:BoolDSL p
                 -> {v:DSLValue p | eval e ρ == Just v}
                 -> { v == VF 0 || v == VF 1 } @-}
booleanProof :: (Fractional p, Eq p)
             => NameValuation p -> DSL p -> DSLValue p -> Proof
booleanProof ρ e _ = case eval e ρ of Just _ -> trivial

{-@ booleanProof' :: m:Nat
                  -> σ:WireValuation p m
                  -> e:{LDSL p (Btwn 0 m) | booleanE e}
                  -> { coherentE m e σ => boolean (M.lookup' (outputWire e) σ) } @-}
booleanProof' :: (Fractional p, Eq p)
             => Int -> WireValuation p -> LDSL p Int -> Proof
booleanProof' m σ e = undefined


-- workarounds to fix "crash: unknown constant"

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
