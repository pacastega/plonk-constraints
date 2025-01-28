{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Optimizations.RemoveConstants (removeConstants) where

import Optimizations.Base
import DSL
import Utils

import Language.Haskell.Liquid.ProofCombinators

{-@ removeConstants :: Opt p @-}
removeConstants :: (Fractional p, Eq p) => DSL p -> Maybe (DSL p)
removeConstants program@(ADD arg1 arg2) = case arg1 of
  -- linear combinations
  MULC p1 k1 -> case arg2 of
    MULC p2 k2 -> let p' = LINCOMB k1 p1 k2 p2 in Just p' ? lemma p' program
    p2         -> let p' = LINCOMB k1 p1 1  p2 in Just p' ? lemma p' program

  CONST 0 -> Just arg2 ? lemma arg2 program
  BIT False -> Just arg2 ? lemma arg2 program

  CONST k -> let p' = ADDC arg2 k in Just p' ? lemma p' program
  BIT True -> let p' = ADDC arg2 1 in Just p' ? lemma p' program

  p1 -> case arg2 of
    MULC p2 k2 -> let p' = LINCOMB 1  p1 k2 p2 in Just p' ? lemma p' program
    CONST 0 -> Just p1 ? lemma p1 program
    BIT False -> Just p1 ? lemma p1 program

    CONST k -> let p' = ADDC arg1 k in Just p' ? lemma p' program
    BIT True -> let p' = ADDC arg1 1 in Just p' ? lemma p' program

    _ -> Nothing

removeConstants program@(SUB arg1 arg2) = case (arg1,arg2) of
  -- subtracting 0 is a no-op
  (p1, CONST 0) -> let p' = p1 in Just p' ? lemma p' program
  -- subtracting a constant can be done more efficiently
  (p1, CONST k) -> let p' = (ADDC p1 (-k)) in Just p' ? lemma p' program

  _ -> Nothing

removeConstants program@(MUL arg1 arg2) = case arg1 of

  CONST 1 -> let p' = arg2 in Just p' ? lemma p' program
  BIT True -> let p' = arg2 in Just p' ? lemma p' program

  CONST 0 -> let p' = CONST 0 in Just p' ? lemma p' program
  BIT False -> let p' = CONST 0 in Just p' ? lemma p' program

  CONST k -> let p' = MULC arg2 k in Just p' ? lemma p' program

  p -> case arg2 of
    CONST 1 -> let p' = arg1 in Just p' ? lemma p' program
    BIT True -> let p' = arg1 in Just p' ? lemma p' program

    CONST 0 -> let p' = CONST 0 in Just p' ? lemma p' program
    BIT False -> let p' = CONST 0 in Just p' ? lemma p' program

    CONST k -> let p' = MULC arg1 k in Just p' ? lemma p' program

    _ -> Nothing

removeConstants program@(DIV arg1 arg2) = case (arg1,arg2) of
  -- dividing by 1 is a no-op
  (p1, CONST 1) -> let p' = p1 in Just p' ? lemma p' program
  -- dividing by a constant can be done more efficiently
  (p1, CONST k) | k /= 0 -> let p' = MULC p1 (1/k) in Just p' ? lemma p' program
  _ -> Nothing

removeConstants program@(EQL arg1 arg2) = case (arg1,arg2) of
  -- checking equality against a constant can be done more efficiently
  (p, CONST k) -> Just (EQLC p k)
  (CONST k, p) -> Just (EQLC p k)
  _ -> Nothing

removeConstants _ = Nothing -- any other pattern is not a redex


-- any "numeric" value is compatible with any "field" value (i.e. it can be used
-- in its place)
{-@ lemma :: d1:{DSL p | numeric d1} -> d2:{DSL p | typed d2 TF}
        -> {compatible d1 d2} @-}
lemma :: DSL p -> DSL p -> Proof
lemma d1 d2 = case (inferType d1, inferType d2) of
  (Just τ1, Just τ2) -> case (τ1, τ2) of
    (TVec _, _) -> trivial
    (_, TVec _) -> trivial
    (_, _) -> trivial
  (_,_) -> trivial
