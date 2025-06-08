{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Semantics where

import DSL
import Utils
import Vec

import qualified Data.Map as M

import Language.Haskell.Liquid.ProofCombinators ((?))

type Valuation p = M.Map String p

-- reflectable valuation
data DSLValue p = VF p | VBool Bool | VVecNil | VVecCons (DSLValue p) (DSLValue p)
type ValuationRefl p = [(String, p)]

{-@ measure valSize @-}
valSize :: DSLValue p -> Int
valSize (VF _)          = 1
valSize (VBool _)       = 1
valSize (VVecNil)       = 0
valSize (VVecCons x xs) = valSize x + valSize xs

-- FIXME: ideally, vectors would be encoded as a single constructor for DSLValue
-- that takes a Haskell list of other DSLValue's, and valSize could call the
-- function 'go' below, but it doesn't seem to work

-- {-@ measure go @-}
-- go :: [DSLValue p] -> Int
-- go [] = 0
-- go (x:xs) = valSize x + go xs

{-@ type FValue p = {v:DSLValue p | isVF v} @-}
{-@ reflect isVF @-}
isVF :: (Num p, Eq p) => DSLValue p -> Bool
isVF = hasType TF

{-@ type BoolValue p = {v:DSLValue p | isVBool v} @-}
{-@ reflect isVBool @-}
isVBool :: (Num p, Eq p) => DSLValue p -> Bool
isVBool = hasType TBool

-- {-@ reflect agreesWith @-}
{-@ inline agreesWith @-}
{-@ agreesWith :: TypedDSL p -> DSLValue p -> Bool @-}
agreesWith :: (Num p, Eq p) => DSL p -> DSLValue p -> Bool
agreesWith p v = case inferType p of
  Just τ  -> hasType τ v

{-@ reflect hasType @-}
{-@ hasType :: τ:Ty -> val:DSLValue p -> Bool / [valSize val] @-}
hasType :: (Num p, Eq p) => Ty -> DSLValue p -> Bool
hasType TF         (VF _)    = True      -- unrestricted values
hasType TBool      (VBool _) = True      -- unrestricted values
hasType (TVec τ n) v =
    if n == 0
    then case v of
      VVecNil -> True
      _       -> False
    else case v of
      VVecCons x xs -> hasType τ x && hasType (TVec τ (n-1)) xs
      _             -> False
hasType _          _               = False



{-@ reflect assertFValue @-}
{-@ assertFValue :: Maybe (FValue p) -> Maybe (FValue p) @-}
assertFValue :: Maybe (DSLValue p) -> Maybe (DSLValue p)
assertFValue = id


{-@ reflect eval @-}
{-@ eval :: program:TypedDSL p -> ValuationRefl p
         -> Maybe ({v:DSLValue p | agreesWith program v }) @-}
eval :: (Fractional p, Eq p) => DSL p -> ValuationRefl p -> Maybe (DSLValue p)
eval program v = case program of
  VAR name τ -> lookup name v >>=
    (\value -> case τ of
        TBool -> case value of
          0 -> Just (VBool False)
          1 -> Just (VBool True)
          _ -> Nothing
        TF -> Just (VF value))
  CONST x -> Just (VF x)
  BOOLEAN b -> Just (VBool b)

  -- Arithmetic operations
  ADD p1 p2 -> liftA2' add (eval p1 v) (eval p2 v)
  SUB p1 p2 -> liftA2' sub (eval p1 v) (eval p2 v)
  MUL p1 p2 -> liftA2' mul (eval p1 v) (eval p2 v)
  DIV p1 p2 -> case (eval p1 v, eval p2 v) of
    (Just (VF x), Just (VF y)) -> if y /= 0 then Just (VF (x / y)) else Nothing
    _ -> Nothing

  ADDC p1 k -> fmap' (add (VF k)) (eval p1 v)
  MULC p1 k -> fmap' (mul (VF k)) (eval p1 v)
  LINCOMB k1 p1 k2 p2 -> liftA2' (linCombFn k1 k2) (eval p1 v) (eval p2 v)

  -- Boolean operations
  NOT p1    -> fmap'   notFn (eval p1 v)
  AND p1 p2 -> liftA2' andFn (eval p1 v) (eval p2 v)
  OR  p1 p2 -> liftA2' orFn  (eval p1 v) (eval p2 v)
  XOR p1 p2 -> liftA2' xorFn (eval p1 v) (eval p2 v)

  UnsafeNOT p1    -> fmap'   notFn (eval p1 v)
  UnsafeAND p1 p2 -> liftA2' andFn (eval p1 v) (eval p2 v)
  UnsafeOR  p1 p2 -> liftA2' orFn  (eval p1 v) (eval p2 v)
  UnsafeXOR p1 p2 -> liftA2' xorFn (eval p1 v) (eval p2 v)

  ISZERO p1 -> fmap' (eqlFn (VF 0)) (eval p1 v)
  EQL p1 p2 -> liftA2' eqlFn        (eval p1 v) (eval p2 v)
  EQLC p1 k -> fmap' (eqlFn (VF k)) (eval p1 v)

  NIL _     -> Just VVecNil
  CONS h ts -> case inferType program of
                Just (TVec τ n) -> liftA2' VVecCons (eval h v) (eval ts v)
                _ -> Nothing

  BoolToF p -> case inferType program of
                -- TODO: this should be Just TF, but that doesn't work
                Just TBool -> fmap' boolToF (eval p v)
                _ -> Nothing

{-@ reflect linCombFn @-}
{-@ linCombFn :: p -> p -> FValue p -> FValue p -> FValue p @-}
linCombFn :: (Num p) => p -> p -> DSLValue p -> DSLValue p -> DSLValue p
linCombFn k1 k2 (VF x) (VF y) = VF (k1*x + k2*y)

{-@ reflect add @-}
{-@ add :: FValue p -> FValue p -> DSLValue p @-}
add :: (Num p) => DSLValue p -> DSLValue p -> DSLValue p
add (VF x) (VF y) = VF (x + y)

{-@ reflect sub @-}
{-@ sub :: FValue p -> FValue p -> DSLValue p @-}
sub :: (Num p) => DSLValue p -> DSLValue p -> DSLValue p
sub (VF x) (VF y) = VF (x - y)

{-@ reflect mul @-}
{-@ mul :: FValue p -> FValue p -> DSLValue p @-}
mul :: (Num p) => DSLValue p -> DSLValue p -> DSLValue p
mul (VF x) (VF y) = VF (x * y)

{-@ reflect notFn @-}
{-@ notFn :: BoolValue p -> DSLValue p @-}
notFn :: (Num p, Eq p) => DSLValue p -> DSLValue p
notFn (VBool b)   = VBool (not b)

{-@ reflect andFn @-}
{-@ andFn :: BoolValue p -> BoolValue p -> DSLValue p @-}
andFn :: (Num p, Eq p) => DSLValue p -> DSLValue p -> DSLValue p
andFn (VBool b) (VBool c) = VBool (b && c)

{-@ reflect orFn @-}
{-@ orFn :: BoolValue p -> BoolValue p -> DSLValue p @-}
orFn :: (Num p, Eq p) => DSLValue p -> DSLValue p -> DSLValue p
orFn  (VBool b) (VBool c) = VBool (b || c)

{-@ reflect xorFn @-}
{-@ xorFn :: BoolValue p -> BoolValue p -> DSLValue p @-}
xorFn :: (Num p, Eq p) => DSLValue p -> DSLValue p -> DSLValue p
xorFn (VBool b) (VBool c) = VBool (b /= c)

{-@ reflect eqlFn @-}
{-@ eqlFn :: FValue p -> FValue p -> DSLValue p @-}
eqlFn :: (Num p, Eq p) => DSLValue p -> DSLValue p -> DSLValue p
eqlFn (VF b) (VF c) = VBool (b == c)

{-@ reflect boolToF @-}
{-@ boolToF :: BoolValue p -> FValue p @-}
boolToF :: (Num p, Eq p) => DSLValue p -> DSLValue p
boolToF (VBool False) = VF 0
boolToF (VBool True)  = VF 1
