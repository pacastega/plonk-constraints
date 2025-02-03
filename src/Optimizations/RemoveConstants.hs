{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Optimizations.RemoveConstants (removeConstants) where

import Optimizations.Base (Opt)
import DSL
import Utils (any')

{-@ removeConstants :: Opt p @-}
removeConstants :: (Fractional p, Eq p) => DSL p -> Maybe (DSL p)
removeConstants (ADD arg1 arg2) = case arg1 of
  -- linear combinations
  MULC p1 k1 -> case arg2 of
    MULC p2 k2 -> let p' = LINCOMB k1 p1 k2 p2 in Just p'
    p2         -> let p' = LINCOMB k1 p1 1  p2 in Just p'

  CONST 0 -> Just arg2
  CONST k -> let p' = ADDC arg2 k in Just p'

  p1 -> case arg2 of
    MULC p2 k2 -> let p' = LINCOMB 1  p1 k2 p2 in Just p'

    CONST 0 -> Just p1
    CONST k -> let p' = ADDC arg1 k in Just p'

    _ -> Nothing

removeConstants (SUB arg1 arg2) = case (arg1,arg2) of
  -- subtracting 0 is a no-op
  (p1, CONST 0) -> let p' = p1 in Just p'
  -- subtracting a constant can be done more efficiently
  (p1, CONST k) -> let p' = (ADDC p1 (-k)) in Just p'

  _ -> Nothing

removeConstants (MUL arg1 arg2) = case arg1 of

  CONST 1 -> let p' = arg2 in Just p'
  CONST 0 -> let p' = CONST 0 in Just p'
  CONST k -> let p' = MULC arg2 k in Just p'

  p -> case arg2 of
    CONST 1 -> let p' = arg1 in Just p'
    CONST 0 -> let p' = CONST 0 in Just p'
    CONST k -> let p' = MULC arg1 k in Just p'

    _ -> Nothing

removeConstants (DIV arg1 arg2) = case (arg1,arg2) of
  -- dividing by 1 is a no-op
  (p1, CONST 1) -> let p' = p1 in Just p'
  -- dividing by a constant can be done more efficiently
  (p1, CONST k) | k /= 0 -> let p' = MULC p1 (1/k) in Just p'

  _ -> Nothing

removeConstants (EQL arg1 arg2) = case (arg1,arg2) of
  -- checking equality against a constant can be done more efficiently
  (p, CONST k) -> Just (EQLC p k)
  (CONST k, p) -> Just (EQLC p k)

  _ -> Nothing

removeConstants _ = Nothing -- any other pattern is not a redex
