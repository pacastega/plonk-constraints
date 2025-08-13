{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

module LabelingProof where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import Utils
import TypeAliases

import Vec
import DSL
import Label
import WitnessGeneration

import Semantics

import Language.Haskell.Liquid.ProofCombinators


--TODO: these should be in DSL.hs instead
{-@ reflect assertionHolds @-}
{-@ assertionHolds :: NameValuation p -> Assertion p -> Bool @-}
assertionHolds :: (Fractional p, Eq p) => NameValuation p -> Assertion p -> Bool
assertionHolds _ (DEF {})  = True -- dummy case
assertionHolds ρ (NZERO e) = case eval e ρ of
  Nothing     -> False
  Just (VF x) -> x /= 0
  _           -> error "impossible"
assertionHolds ρ (BOOL e) = case eval e ρ of
  Nothing     -> False
  Just (VF x) -> boolean x
  _           -> error "impossible"
assertionHolds ρ (EQA e1 e2) = case (eval e1 ρ, eval e2 ρ) of
  (Nothing, _)                 -> False
  (_, Nothing)                 -> False
  (Just (VF v1), Just (VF v2)) -> v1 == v2

  (Just VVecNil,_)        -> error "impossible"
  (Just (VVecCons _ _),_) -> error "impossible"
  (_,Just VVecNil)        -> error "impossible"
  (_,Just (VVecCons _ _)) -> error "impossible"

  _ -> False -- ?? there are no more cases left


{-@ reflect assertionsHold @-}
assertionsHold :: (Fractional p, Eq p) => NameValuation p -> Store p -> Bool
assertionsHold ρ = all' (assertionHolds ρ)


{-@ reflect semanticsHold @-}
{-@ semanticsHold :: m:Nat -> VecN p m -> [LDSL p (Btwn 0 m)] -> Bool @-}
semanticsHold :: (Fractional p, Eq p) => Int -> Vec p -> [LDSL p Int] -> Bool
semanticsHold m σ = all' (\x -> semanticsAreCorrect m x σ)


{-@ reflect mkList1 @-}
mkList1 :: a -> [a]
mkList1 x = [x]


--TODO: this should be in DSL.hs
{-@ reflect barSigma @-}
{-@ barSigma :: m:Nat -> σ:VecN p m -> [LDSL p (Btwn 0 m)] -> [DSLValue p] @-}
barSigma :: Int -> Vec p -> [LDSL p Int] -> [DSLValue p]
barSigma m σ es = map' (\e -> VF (σ ! (outputWire e))) es


{-@ reflect factorsThrough @-}
{-@ factorsThrough :: m:Nat
                   -> σ:VecN p m -> λ:LabelEnv p (Btwn 0 m)
                   -> ρ:NameValuation p
                   -> Bool @-}
factorsThrough :: Eq p => Int -> Vec p -> LabelEnv p Int -> NameValuation p -> Bool
factorsThrough _ σ λ ρ =
  all' (\(name,value) -> case M.lookup name λ of
           --TODO: prove that keysSet ρ ⊆ keysSet λ
                           Nothing -> True -- this should not happen
                           Just index -> σ!index == value)
         (M.toList ρ)


-- this corresponds to Lemma 1. from the paper
{-@ lemma :: m':Nat -> m:{Nat | m >= m'}
          -> e:{TypedDSL p | scalar e}
          -> as:Store p
          -> ρ:NameValuation p
          -> λ:LabelEnv p (Btwn 0 m) -> λ':LabelEnv p (Btwn 0 m)
          -> {as':[LDSL p (Btwn 0 m)] |
                  labelStore as 0 M.MTip = (m', as', λ')}
          -> {es':[LDSL p (Btwn 0 m)] |
                  label' e m' λ' = (m, es', λ)}
          -> σ:{VecN p m | σ = witnessGen m as' ρ}
          -> { factorsThrough m σ λ ρ } @-}
lemma :: Int -> Int -> DSL p -> Store p -> NameValuation p
      -> LabelEnv p Int -> LabelEnv p Int
      -> [LDSL p Int] -> [LDSL p Int] -> Vec p
      -> Proof
lemma = undefined -- assume it holds for now


-- this corresponds to Lemma 2. from the paper
{-@ labelProof1 :: m':Nat -> m:{Nat | m >= m'}
                -> e:{TypedDSL p | scalar e}
                -> ρ:NameValuation p
                -> λ:LabelEnv p (Btwn 0 m) -> λ':LabelEnv p (Btwn 0 m')
                -> {es':[LDSL p (Btwn 0 m)] |
                        label' e m' λ' = (m, es', λ)}
                -> σ:{VecN p m | σ = witnessGen m es' ρ}
                -> v:DSLValue p
                -> {eval e ρ = Just v <=> barSigma m σ es' = mkList1 v} @-}
-- semanticsHold m σ es'
labelProof1 :: (Fractional p, Eq p, Ord p)
            => Int -> Int -> DSL p
            -> NameValuation p
            -> LabelEnv p Int -> LabelEnv p Int
            -> [LDSL p Int]
            -> Vec p
            -> DSLValue p
            -> Proof
labelProof1 m' m e ρ λ λ' es' σ v = case e of
  VAR _ _ -> trivial -- undefined
  CONST _ -> undefined
  BOOLEAN _ -> undefined

  ADD _ _ -> undefined
  SUB _ _ -> undefined
  MUL _ _ -> undefined
  DIV _ _ -> undefined

  ADDC _ _ -> undefined
  MULC _ _ -> undefined
  LINCOMB _ _ _ _ -> undefined

  NOT _ -> undefined
  AND _ _ -> undefined
  OR _ _ -> undefined
  XOR _ _ -> undefined

  UnsafeNOT _ -> undefined
  UnsafeAND _ _ -> undefined
  UnsafeOR _ _ -> undefined
  UnsafeXOR _ _ -> undefined

  ISZERO _ -> undefined
  EQL _ _ -> undefined
  EQLC _ _ -> undefined

  NIL _ -> error "vectors are not scalar"
  CONS h ts -> undefined

  BoolToF _ -> undefined
labelProof1 m' m e ρ λ λ' es' σ v = case label' e m' λ' of
  (_, _, _) -> error "the length is 1"


-- This is Theorem 2.
{-@ labelProof :: m':Nat -> m:{Nat | m >= m'}
               -> e:{TypedDSL p | scalar e}
               -> as:Store p
               -> ρ:NameValuation p
               -> λ:LabelEnv p (Btwn 0 m) -> λ':LabelEnv p (Btwn 0 m)
               -> {as':[LDSL p (Btwn 0 m)] |
                       labelStore as 0 M.MTip = (m', as', λ')}
               -> {es':[LDSL p (Btwn 0 m)] |
                       label' e m' λ' = (m, es', λ)}
               -> σ:{VecN p m | σ = witnessGen m as' ρ}
               -> {assertionsHold ρ as <=> semanticsHold m σ as'} @-}
labelProof :: (Fractional p, Eq p) => Int -> Int -> DSL p -> Store p
           -> NameValuation p
           -> LabelEnv p Int -> LabelEnv p Int
           -> [LDSL p Int] -> [LDSL p Int]
           -> Vec p
           -> Proof
labelProof m' m e []     ρ λ λ' as' es' σ = trivial
labelProof m' m e (a:as) ρ λ λ' as' es' σ = case a of
  DEF _ _ _ -> undefined -- dummy
  NZERO p1  -> undefined -- IH missing
  BOOL p1   -> undefined -- IH missing
  EQA p1 p2 -> undefined -- IH missing
