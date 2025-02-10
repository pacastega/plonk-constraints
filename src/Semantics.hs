{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Semantics where

import DSL
import Utils
import Vec

import qualified Data.Map as M

{-@ type Valuation p = M.Map String p @-}
type Valuation p = M.Map String p

-- reflectable valuation
type ValuationRefl p = [(String, p)]

-- TODO: how to deal with vectors? just forbid them in the precondition?
{-@ reflect eval @-}
{-@ eval :: {v:DSL p | scalar v} -> ValuationRefl p -> Maybe p @-}
eval :: (Fractional p, Eq p) => DSL p -> ValuationRefl p -> Maybe p
eval program v = case program of
  VAR name _ -> lookup name v
  CONST x -> Just x
  BOOLEAN True -> Just 1
  BOOLEAN False -> Just 0

  -- Arithmetic operations
  -- assert (any' numericType (inferType p1))
  ADD p1 p2 -> liftA2' add (eval p1 v) (eval p2 v)
  SUB p1 p2 -> liftA2' sub (eval p1 v) (eval p2 v)
  MUL p1 p2 -> liftA2' mul (eval p1 v) (eval p2 v)
  DIV p1 p2 -> case (eval p1 v, eval p2 v) of
    (Just x, Just y) -> if y /= 0 then Just (x / y) else Nothing
    _ -> Nothing

  ADDC p1 k -> fmap' ((+) k) (eval p1 v)
  MULC p1 k -> fmap' ((*) k) (eval p1 v)
  LINCOMB k1 p1 k2 p2 -> liftA2' (linCombFn k1 k2) (eval p1 v) (eval p2 v)

  -- Boolean operations (assume inputs are binary)
  NOT p1    -> fmap'   notFn (eval p1 v)
  AND p1 p2 -> liftA2' andFn (eval p1 v) (eval p2 v)
  OR  p1 p2 -> liftA2' orFn  (eval p1 v) (eval p2 v)
  XOR p1 p2 -> liftA2' xorFn (eval p1 v) (eval p2 v)

  UnsafeNOT p1    -> fmap'   notFn (eval p1 v)
  UnsafeAND p1 p2 -> liftA2' andFn (eval p1 v) (eval p2 v)
  UnsafeOR  p1 p2 -> liftA2' orFn  (eval p1 v) (eval p2 v)
  UnsafeXOR p1 p2 -> liftA2' xorFn (eval p1 v) (eval p2 v)

  ISZERO p1 -> fmap' (eqlFn 0) (eval p1 v)
  EQL p1 p2 -> liftA2' eqlFn   (eval p1 v) (eval p2 v)
  EQLC p1 k -> fmap' (eqlFn k) (eval p1 v)

  BoolToF p -> eval p v

{-@ reflect linCombFn @-}
linCombFn :: (Num p) => p -> p -> p -> p -> p
linCombFn k1 k2 x y = k1*x + k2*y

{-@ reflect add @-}
add :: (Num p) => p -> p -> p
add x y = x + y

{-@ reflect sub @-}
sub :: (Num p) => p -> p -> p
sub x y = x - y

{-@ reflect mul @-}
mul :: (Num p) => p -> p -> p
mul x y = x * y

{-@ reflect notFn @-}
notFn :: (Num p, Eq p) => p -> p
notFn x   = if x == 1 then 0 else 1

{-@ reflect andFn @-}
andFn :: (Num p, Eq p) => p -> p -> p
andFn x y = if x == 0 || y == 0 then 0 else 1

{-@ reflect orFn @-}
orFn :: (Num p, Eq p) => p -> p -> p
orFn  x y = if x == 1 || y == 1 then 1 else 0

{-@ reflect xorFn @-}
xorFn :: (Num p, Eq p) => p -> p -> p
xorFn x y = if x /= y then 1 else 0

{-@ reflect eqlFn @-}
eqlFn :: (Num p, Eq p) => p -> p -> p
eqlFn x y = if x == y then 1 else 0
