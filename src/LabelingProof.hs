{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module LabelingProof where

import qualified Liquid.Data.Map as M

import Utils
import TypeAliases

import Vec
import DSL
import Label
import WitnessGeneration

import Semantics

import Language.Haskell.Liquid.ProofCombinators


{-@ reflect assertionHolds @-}
{-@ assertionHolds :: ValuationRefl p -> Assertion p -> Bool @-}
assertionHolds :: (Fractional p, Eq p) => ValuationRefl p -> Assertion p -> Bool
assertionHolds _ (DEF {})  = True -- dummy case
assertionHolds v (NZERO e) = case eval e v of
  Nothing     -> False
  Just (VF x) -> x /= 0
  _           -> error "impossible"
assertionHolds v (BOOL e) = case eval e v of
  Nothing     -> False
  Just (VF x) -> boolean x
  _           -> error "impossible"
assertionHolds v (EQA e1 e2) = case (eval e1 v, eval e2 v) of
  (Just (VF v1), Just (VF v2)) -> v1 == v2
  _                            -> error "impossible"


{-@ reflect all' @-}
all' :: (a -> Bool) -> [a] -> Bool
all' _ [] = True
all' p (x:xs) = p x && all' p xs

{-@ reflect assertionsHold @-}
assertionsHold :: (Fractional p, Eq p) => ValuationRefl p -> Store p -> Bool
assertionsHold ρ = all' (assertionHolds ρ)


{-@ reflect semanticsHold @-}
{-@ semanticsHold :: m:Nat -> VecN p m -> [LDSL p (Btwn 0 m)] -> Bool @-}
semanticsHold :: (Fractional p, Eq p) => Int -> Vec p -> [LDSL p Int] -> Bool
semanticsHold m σ = all' (\x -> semanticsAreCorrect m x σ)


{-@ labelProof :: m':Nat -> m:{Nat | m >= m'}
               -> e:TypedDSL p
               -> as:Store p
               -> ρ:ValuationRefl p
               -> λ:Env p (Btwn 0 m) -> λ':Env p (Btwn 0 m)
               -> {as':[LDSL p (Btwn 0 m)] |
                       labelStore as 0 M.empty = (m', as', λ')}
               -> {es':[LDSL p (Btwn 0 m)] |
                       label' e m' λ' = (m, es', λ)}
               -> σ:{VecN p m | σ = witnessGen m as' ρ}
               -> {assertionsHold as ρ <=> semanticsHold m σ as'} @-}
labelProof :: (Fractional p, Eq p) => Int -> Int -> DSL p -> Store p
           -> ValuationRefl p
           -> Env p Int -> Env p Int
           -> [LDSL p Int] -> [LDSL p Int]
           -> Vec p
           -> Proof
labelProof = undefined
