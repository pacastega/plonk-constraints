{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

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


--TODO: these should be in DSL.hs instead
{-@ reflect assertionHolds @-}
{-@ assertionHolds :: ValuationRefl p -> Assertion p -> Bool @-}
assertionHolds :: (Fractional p, Eq p) => ValuationRefl p -> Assertion p -> Bool
assertionHolds _ (DEF {})  = True -- dummy case
assertionHolds v (NZERO e) = case eval e v of
  Nothing     -> False
  Just (VF x) -> x /= 0
  Just (VBool b) -> b -- b /= False
  _           -> error "impossible"
assertionHolds v (BOOL e) = case eval e v of
  Nothing     -> False
  Just (VF x) -> boolean x
  Just (VBool _) -> True
  _           -> error "impossible"
assertionHolds v (EQA e1 e2) = case (eval e1 v, eval e2 v) of
  (Nothing, _)                 -> False
  (_, Nothing)                 -> False
  (Just (VF v1), Just (VF v2)) -> v1 == v2
  (Just (VBool b1), Just (VBool b2)) -> b1 == b2
  (Just (VF v1)   , Just (VBool b2)) -> v1 == (if b2 then 1 else 0)
  (Just (VBool b1), Just (VF v2))    -> (if b1 then 1 else 0) == v2

  (Just VVecNil,_)        -> error "impossible"
  (Just (VVecCons _ _),_) -> error "impossible"
  (_,Just VVecNil)        -> error "impossible"
  (_,Just (VVecCons _ _)) -> error "impossible"

  _ -> False -- ?? there are no more cases left


{-@ reflect assertionsHold @-}
assertionsHold :: (Fractional p, Eq p) => ValuationRefl p -> Store p -> Bool
assertionsHold ρ = all' (assertionHolds ρ)


{-@ reflect semanticsHold @-}
{-@ semanticsHold :: m:Nat -> VecN p m -> [LDSL p (Btwn 0 m)] -> Bool @-}
semanticsHold :: (Fractional p, Eq p) => Int -> Vec p -> [LDSL p Int] -> Bool
semanticsHold m σ = all' (\x -> semanticsAreCorrect m x σ)


--TODO: this should be in Utils.hs instead
{-@ reflect all' @-}
all' :: (a -> Bool) -> [a] -> Bool
all' _ [] = True
all' p (x:xs) = p x && all' p xs

{-@ reflect mkList1 @-}
mkList1 :: a -> [a]
mkList1 x = [x]


--TODO: this should be in DSL.hs
{-@ reflect barSigma @-}
{-@ barSigma :: m:Nat -> σ:VecN p m -> [LDSL p (Btwn 0 m)] -> [DSLValue p] @-}
barSigma :: Int -> Vec p -> [LDSL p Int] -> [DSLValue p]
barSigma m σ es = map' (\e -> VF (σ ! (outputWire e))) es


{-@ labelProof1 :: m':Nat -> m:{Nat | m >= m'}
                -> e:{TypedDSL p | scalar e}
                -> ρ:ValuationRefl p
                -> λ:Env p (Btwn 0 m) -> λ':Env p (Btwn 0 m)
                -> {es':[LDSL p (Btwn 0 m)] |
                        label' e m' λ' = (m, es', λ)}
                -> σ:{VecN p m | σ = witnessGen m es' ρ}
                -> v:DSLValue p
                -> {eval e ρ = Just v <=> barSigma m σ es' = mkList1 v} @-}
-- semanticsHold m σ es'
labelProof1 :: Int -> Int -> DSL p
            -> ValuationRefl p
            -> Env p Int -> Env p Int
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


{-@ labelProof :: m':Nat -> m:{Nat | m >= m'}
               -> e:{TypedDSL p | scalar e}
               -> as:Store p
               -> ρ:ValuationRefl p
               -> λ:Env p (Btwn 0 m) -> λ':Env p (Btwn 0 m)
               -> {as':[LDSL p (Btwn 0 m)] |
                       labelStore as 0 M.MTip = (m', as', λ')}
               -> {es':[LDSL p (Btwn 0 m)] |
                       label' e m' λ' = (m, es', λ)}
               -> σ:{VecN p m | σ = witnessGen m as' ρ}
               -> {assertionsHold ρ as <=> semanticsHold m σ as'} @-}
labelProof :: (Fractional p, Eq p) => Int -> Int -> DSL p -> Store p
           -> ValuationRefl p
           -> Env p Int -> Env p Int
           -> [LDSL p Int] -> [LDSL p Int]
           -> Vec p
           -> Proof
labelProof m' m e []     ρ λ λ' as' es' σ = trivial
labelProof m' m e (a:as) ρ λ λ' as' es' σ = case a of
  DEF _ _ _ -> undefined -- dummy
  NZERO p1  -> undefined -- IH missing
  BOOL p1   -> undefined -- IH missing
  EQA p1 p2 -> undefined -- IH missing
