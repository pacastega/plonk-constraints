{-# LANGUAGE ScopedTypeVariables #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--save" @-}
{- LIQUID "--case-expand=20" @-}
module Semantics where

import DSL
import Utils
import Vec

import qualified Data.Map as M

import Language.Haskell.Liquid.ProofCombinators ((?))

type Valuation p = M.Map String p

-- reflectable valuation
data DSLValue p = VF p | VBool Bool | VVecNil | VVecCons (DSLValue p) (DSLValue p)
--TODO: VBool could take a Bool instead of a p
type ValuationRefl p = [(String, DSLValue p)]

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
-- hasType (TVec τ 0) (VVecNil)       = True
-- hasType (TVec τ n) (VVecCons x xs) = 
--                                        hasType τ x
                                   -- && 
                                   -- hasType (TVec τ (n-1)) xs

hasType _          _               = False



{-@ reflect assertFValue @-}
{-@ assertFValue :: Maybe (FValue p) -> Maybe (FValue p) @-}
assertFValue :: Maybe (DSLValue p) -> Maybe (DSLValue p)
assertFValue = id


{-@ eval :: program:TypedDSL p -> ValuationRefl p
         -> Maybe ({v:DSLValue p | agreesWith program v }) @-}
eval :: (Fractional p, Eq p) => DSL p  -> ValuationRefl p -> Maybe (DSLValue p)
eval program v = case inferType program of
                    Just typ -> evalTyped program typ v
                    Nothing  -> Nothing



-- {-@ reflect eval @-}
{-@ evalTyped :: program:TypedDSL p -> typ:{Ty |  inferType program == Just typ} -> ValuationRefl p
         -> Maybe ({v:DSLValue p | agreesWith program v && hasType typ v }) @-}
evalTyped :: (Fractional p, Eq p) => DSL p -> Ty -> ValuationRefl p -> Maybe (DSLValue p)
evalTyped program typ v = case program of
  VAR name τ -> lookup name v >>= (\value -> if hasType τ value
                                             then Just value else Nothing)
  CONST x -> Just (VF x)
  BOOLEAN b -> Just (VBool b)

  -- Arithmetic operations
  ADD p1 p2 -> liftA2' add (evalTyped p1 TF v) (evalTyped p2 TF v)
  SUB p1 p2 -> liftA2' sub (evalTyped p1 TF v) (evalTyped p2 TF v)
  MUL p1 p2 -> liftA2' mul (evalTyped p1 TF v) (evalTyped p2 TF v)
  DIV p1 p2 -> case (evalTyped p1 TF v, evalTyped p2 TF v) of
    (Just (VF x), Just (VF y)) -> if y /= 0 then Just (VF (x / y)) else Nothing
    _ -> Nothing

  ADDC p1 k -> fmap' (add (VF k)) (evalTyped p1 TF v)
  MULC p1 k -> fmap' (mul (VF k)) (evalTyped p1 TF v)
  LINCOMB k1 p1 k2 p2 -> liftA2' (linCombFn k1 k2) (evalTyped p1 TF v) (evalTyped p2 TF v)

  -- TODO: the rest of the cases don't pass, maybe for the same reason as the
  -- 'boolean' issue in lines 84-85 above

  -- Boolean operations
  NOT p1    -> fmap'   notFn (evalTyped p1 TBool v)
  AND p1 p2 -> liftA2' andFn (evalTyped p1 TBool v) (evalTyped p2 TBool v)
  OR  p1 p2 -> liftA2' orFn  (evalTyped p1 TBool v) (evalTyped p2 TBool v)
  XOR p1 p2 -> liftA2' xorFn (evalTyped p1 TBool v) (evalTyped p2 TBool v)

  UnsafeNOT p1    -> fmap'   notFn (evalTyped p1 TBool v)
  UnsafeAND p1 p2 -> liftA2' andFn (evalTyped p1 TBool v) (evalTyped p2 TBool v)
  UnsafeOR  p1 p2 -> liftA2' orFn  (evalTyped p1 TBool v) (evalTyped p2 TBool v)
  UnsafeXOR p1 p2 -> liftA2' xorFn (evalTyped p1 TBool v) (evalTyped p2 TBool v)

  ISZERO p1 -> fmap' (eqlFn (VF 0)) (evalTyped p1 TF v)
  EQL p1 p2 -> liftA2' eqlFn        (evalTyped p1 TF v) (evalTyped p2 TF v)
  EQLC p1 k -> fmap' (eqlFn (VF k)) (evalTyped p1 TF v)

  NIL _     -> Just VVecNil
  CONS h ts -> case inferType program of 
                Just (TVec tt n) -> liftA2' VVecCons (evalTyped h tt v) (evalTyped ts (TVec tt (n-1)) v) 
                _ -> Nothing

  BoolToF p -> undefined -- fmap' boolToF (eval p v)



{-@ inline assert @-}
{-@ assert :: {v:Bool | v} -> y:a -> {x:a | v && x = y} @-}
assert :: Bool -> a -> a 
assert _ x = x

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

{-@ boolToF :: BoolValue p -> FValue p @-}
boolToF :: (Num p, Eq p) => DSLValue p -> DSLValue p
boolToF (VBool False) = VF 0
boolToF (VBool True)  = VF 1
