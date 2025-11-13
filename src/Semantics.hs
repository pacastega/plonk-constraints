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

  UN op p1 -> case op of
    ADDC k    -> fmap' (add (VF k))   (eval p1 ρ)
    MULC k    -> fmap' (mul (VF k))   (eval p1 ρ)

    NOT       -> fmap' notFn          (eval p1 ρ)
    UnsafeNOT -> fmap' notFn          (eval p1 ρ)

    ISZERO    -> fmap' (eqlFn (VF 0)) (eval p1 ρ)
    EQLC k    -> fmap' (eqlFn (VF k)) (eval p1 ρ)

    BoolToF   -> eval p1 ρ

  BIN op p1 p2 -> case op of
    ADD -> liftA2' add (eval p1 ρ) (eval p2 ρ)
    SUB -> liftA2' sub (eval p1 ρ) (eval p2 ρ)
    MUL -> liftA2' mul (eval p1 ρ) (eval p2 ρ)
    DIV -> case (eval p1 ρ, eval p2 ρ) of
      (Just (VF x), Just (VF y)) -> if y /= 0 then Just (VF (x / y)) else Nothing
      _ -> Nothing

    LINCOMB k1 k2 -> liftA2' (linCombFn k1 k2) (eval p1 ρ) (eval p2 ρ)

    AND -> liftA2' andFn (eval p1 ρ) (eval p2 ρ)
    OR  -> liftA2' orFn  (eval p1 ρ) (eval p2 ρ)
    XOR -> liftA2' xorFn (eval p1 ρ) (eval p2 ρ)

    UnsafeAND -> liftA2' andFn (eval p1 ρ) (eval p2 ρ)
    UnsafeOR  -> liftA2' orFn  (eval p1 ρ) (eval p2 ρ)
    UnsafeXOR -> liftA2' xorFn (eval p1 ρ) (eval p2 ρ)

    EQL -> liftA2' eqlFn (eval p1 ρ) (eval p2 ρ)

  NIL _     -> Just VNil
  CONS h ts -> liftA2' VCons (eval h ρ) (eval ts ρ)


{-@ reflect linCombFn @-}
{-@ linCombFn :: p -> p -> FValue p -> FValue p -> FValue p @-}
linCombFn :: (Num p) => p -> p -> DSLValue p -> DSLValue p -> DSLValue p
linCombFn k1 k2 (VF x) (VF y) = VF (k1*x + k2*y)

{-@ reflect add @-}
{-@ add :: FValue p -> FValue p -> FValue p @-}
add :: (Num p) => DSLValue p -> DSLValue p -> DSLValue p
add (VF x) (VF y) = VF (x + y)

{-@ reflect sub @-}
{-@ sub :: FValue p -> FValue p -> FValue p @-}
sub :: (Num p) => DSLValue p -> DSLValue p -> DSLValue p
sub (VF x) (VF y) = VF (x - y)

{-@ reflect mul @-}
{-@ mul :: FValue p -> FValue p -> FValue p @-}
mul :: (Num p) => DSLValue p -> DSLValue p -> DSLValue p
mul (VF x) (VF y) = VF (x * y)

{-@ reflect notFn @-}
{-@ notFn :: BoolValue p -> BoolValue p @-}
notFn :: (Num p) => DSLValue p -> DSLValue p
notFn (VF b) = VF (1 - b)

{-@ reflect andFn @-}
{-@ andFn :: BoolValue p -> BoolValue p -> BoolValue p @-}
andFn :: (Num p) => DSLValue p -> DSLValue p -> DSLValue p
andFn (VF b) (VF c) = VF (b * c)

{-@ reflect orFn @-}
{-@ orFn :: BoolValue p -> BoolValue p -> BoolValue p @-}
orFn :: (Num p) => DSLValue p -> DSLValue p -> DSLValue p
orFn  (VF b) (VF c) = VF (b + c - b*c)

{-@ reflect xorFn @-}
{-@ xorFn :: BoolValue p -> BoolValue p -> BoolValue p @-}
xorFn :: (Num p) => DSLValue p -> DSLValue p -> DSLValue p
xorFn (VF b) (VF c) = VF (b + c - 2*b*c)

{-@ reflect eqlFn @-}
{-@ eqlFn :: FValue p -> FValue p -> BoolValue p @-}
eqlFn :: (Num p, Eq p) => DSLValue p -> DSLValue p -> DSLValue p
eqlFn (VF b) (VF c) = VF (if b == c then 1 else 0)
