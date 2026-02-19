{-# LANGUAGE ScopedTypeVariables, CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Semantics where

import DSL
import Utils
import Vec

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import Language.Haskell.Liquid.ProofCombinators (withProof)

data DSLValue p = VF p | VNil | VCons (DSLValue p) (DSLValue p)
  deriving Eq

type NameValuation p = M.Map String p

{-@ measure valSize @-}
valSize :: DSLValue p -> Int
valSize (VF _)       = 1
valSize (VNil)       = 0
valSize (VCons x xs) = valSize x + valSize xs

{-@ type FValue p = {v:DSLValue p | hasType TF v} @-}
{-@ type BoolValue p = {v:DSLValue p | hasType TBool v} @-}

-- {-@ reflect agreesWith @-}
{-@ inline agreesWith @-}
{-@ agreesWith :: TypedDSL p -> DSLValue p -> Bool @-}
agreesWith :: (Num p, Eq p) => DSL p -> DSLValue p -> Bool
agreesWith p v = case inferType p of
  Just τ  -> hasType τ v

{-@ reflect hasType @-}
{-@ hasType :: τ:Ty -> val:DSLValue p -> Bool / [valSize val] @-}
hasType :: (Num p, Eq p) => Ty -> DSLValue p -> Bool
hasType TF       (VF _)       = True      -- unrestricted field values
hasType TBool    (VF x)       = boolean x -- field values in {0,1}
hasType (TVec τ) VNil         = True
hasType (TVec τ) (VCons x xs) = hasType τ x && hasType (TVec τ) xs
hasType _         _           = False

{-@ reflect eval @-}
{-@ eval :: expr:TypedDSL p -> NameValuation p
         -> Maybe ({v:DSLValue p | agreesWith expr v}) @-}
eval :: (Fractional p, Eq p) => DSL p -> NameValuation p -> Maybe (DSLValue p)
eval expr ρ = case expr of
  VAR name τ -> case M.lookup name ρ of
    Nothing -> Nothing
    Just value -> case τ of
      TBool -> if boolean value then Just (VF value) else Nothing
      TF    -> Just (VF value)
  CONST x -> Just (VF x)
  BOOL True  -> withProof (Just (VF 1)) (boolean 1)
  BOOL False -> withProof (Just (VF 0)) (boolean 0)

  UN op p1 -> case eval p1 ρ of
    Just (VF x) -> case op of
      ADDC k    -> Just (VF (k + x))
      MULC k    -> Just (VF (k * x))

      NOT       -> Just (VF (notFn x))
      UnsafeNOT -> Just (VF (notFn x))

      ISZERO    -> Just (VF (eqlFn 0 x))
      EQLC k    -> Just (VF (eqlFn k x))

      BoolToF   -> Just (VF x)

    _ -> Nothing -- the argument is undefined

  BIN op p1 p2 -> case (eval p1 ρ, eval p2 ρ) of
    (Just (VF x), Just (VF y)) -> case op of
      ADD -> Just (VF (x + y))
      SUB -> Just (VF (x - y))
      MUL -> Just (VF (x * y))
      DIV -> if y /= 0 then Just (VF (x / y)) else Nothing

      LINCOMB k1 k2 -> Just (VF (k1*x + k2*y))

      AND -> Just (VF (andFn x y))
      OR  -> Just (VF (orFn  x y))
      XOR -> Just (VF (xorFn x y))

      UnsafeAND -> Just (VF (andFn x y))
      UnsafeOR  -> Just (VF (orFn  x y))
      UnsafeXOR -> Just (VF (xorFn x y))

      EQL -> Just (VF (eqlFn x y))

    _ -> Nothing -- at least one of the arguments is undefined

  NIL _     -> Just VNil
  CONS h ts -> liftA2' VCons (eval h ρ) (eval ts ρ)


{-@ reflect notFn @-}
notFn :: (Num p) => p -> p
notFn b = 1 - b

{-@ reflect andFn @-}
andFn :: (Num p) => p -> p -> p
andFn b c = b * c

{-@ reflect orFn @-}
orFn :: (Num p) => p -> p -> p
orFn b c = b + c - b*c

{-@ reflect xorFn @-}
xorFn :: (Num p) => p -> p -> p
xorFn b c = b + c - 2*b*c

{-@ reflect eqlFn @-}
eqlFn :: (Num p, Eq p) => p -> p -> p
eqlFn b c = if b == c then 1 else 0
