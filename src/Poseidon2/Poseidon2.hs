{-# LANGUAGE RecordWildCards, OrPatterns #-}
{-@ LIQUID "--reflection" @-}
{- LIQUID "--eliminate=none" @-}
{-@ LIQUID "--ple" @-}
module Poseidon2.Poseidon2 where

import Utils
import DSL
import PlinkLib
import Poseidon2.Poseidon2Cnst

import Language.Haskell.Liquid.ProofCombinators

{-@ matMulInternal :: ins:Instance F_BLS12 -> VecDSL' F_BLS12 (t ins)
                   -> VecDSL' F_BLS12 (t ins) @-}
matMulInternal :: Instance F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12
matMulInternal (Ins {..}) xs = case t of
  2 -> case xs of
    CONS x0 (CONS x1 (NIL TF)) ->
      fromList TF [ ((CONST 2 `times` x0) `plus` x1)
               , (x0 `plus` (CONST 3 `times` x1)) ]
    -- [x0,x1] -> [2*x0+x1, x0+3*x1], i.e. multiplying by the matrix
    -- [2 1]
    -- [1 3]
  3 -> case xs of
    CONS x0 (CONS x1 (CONS x2 (NIL TF))) ->
      fromList TF [ sum `plus` x0
                  , sum `plus` x1
                  , sum `plus` (CONST 2 `times` x2)]
      where sum = x0 `plus` x1 `plus` x2
    -- i.e. multiplying the input by the matrix
    -- [2 1 1]
    -- [1 2 1]
    -- [1 1 3]
  (4;8;12;16;20;24) -> vZipWith TF TF TF (\x μ -> sum `plus` (μ `times` x)) xs matInternalDiag
    where sum = vSum xs
  _ -> error "this value for t is not supported"

{-@ matMulExternal :: ins:Instance F_BLS12 -> VecDSL' F_BLS12 (t ins)
                   -> VecDSL' F_BLS12 (t ins) @-}
matMulExternal :: Instance F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12
matMulExternal (Ins {..}) xs = case t of
  2 -> case xs of
    CONS x0 (CONS x1 (NIL TF)) ->
      fromList TF [ ((CONST 2 `times` x0) `plus` x1)
                  , x0 `plus` (CONST 2 `times` x1) ]
  3 -> case xs of
    CONS x0 (CONS x1 (CONS x2 (NIL TF))) ->
      fromList TF [sum `plus` x0, sum `plus` x1, sum `plus` x2]
      where sum = x0 `plus` x1 `plus` x2
  4 -> matMulM4 xs
  (8;12;16;20;24) -> matMulM4' xs
  _ -> error "this value for t is not supported"

{-@ matMulM4' :: {v:VecDSL F_BLS12 TF | (vlength v) mod 4 = 0}
              -> {res:VecDSL F_BLS12 TF | vlength res = vlength v} @-}
matMulM4' :: DSL F_BLS12 -> DSL F_BLS12
matMulM4' xs = vConcat TF step2 ? lengthsLemma 4 step2 where

  -- apply matMulM4 separately to each 4-element chunk:
  step1  = map matMulM4 (vChunk TF 4 xs)
  step1 :: [DSL F_BLS12]
  {-@ step1 :: {l:[VecDSL' F_BLS12 4] | 4 * len l = vlength xs} @-}

  -- add components in four groups depending on their remainder modulo 4:
  sums = fold' 4 (vZipWith TF TF TF plus) (vReplicate TF 4 (CONST 0)) step1
  sums :: DSL F_BLS12
  {-@ sums :: VecDSL' F_BLS12 4 @-}

  -- add the sums to each 4-element chunk:
  step2 = map (vZipWith TF TF TF plus sums) step1
  step2 :: [DSL F_BLS12]
  {-@ step2 :: {l:[VecDSL' F_BLS12 4] | 4 * len l = vlength xs} @-}


{-@ matMulM4 :: VecDSL' F_BLS12 4 -> VecDSL' F_BLS12 4 @-}
matMulM4 :: DSL F_BLS12 -> DSL F_BLS12
matMulM4 (CONS x0 (CONS x1 (CONS x2 (CONS x3 (NIL TF))))) =
   fromList TF [t6, t5, t7, t4]
    -- let CSE take care of the repetitions
    where t0 = x0 `plus` x1
          t1 = x2 `plus` x3
          t2 = BIN (LINCOMB 2 1) x1 t1
          t3 = BIN (LINCOMB 2 1) x3 t0
          t4 = BIN (LINCOMB 4 1) t1 t3
          t5 = BIN (LINCOMB 4 1) t0 t2
          t6 = t3 `plus` t5
          t7 = t2 `plus` t4
          {-@ t0 :: FieldDSL F_BLS12 @-}
          {-@ t1 :: FieldDSL F_BLS12 @-}
          {-@ t2 :: FieldDSL F_BLS12 @-}
          {-@ t3 :: FieldDSL F_BLS12 @-}
          {-@ t4 :: FieldDSL F_BLS12 @-}
          {-@ t5 :: FieldDSL F_BLS12 @-}
          {-@ t6 :: FieldDSL F_BLS12 @-}
          {-@ t7 :: FieldDSL F_BLS12 @-}


{-@ sbox :: ins:Instance F_BLS12 -> VecDSL' F_BLS12 (t ins)
         -> VecDSL' F_BLS12 (t ins) @-}
sbox :: Instance F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12
sbox ins = vMap TF TF (sbox_p ins)

{-@ sbox_p :: Instance F_BLS12 -> FieldDSL F_BLS12 -> FieldDSL F_BLS12 @-}
sbox_p :: Instance F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12
sbox_p (Ins {..}) x = let x2 = (x `times` x) in case d of
  -- this parenthesization allows CSE to reuse some subexpressions
  3 -> x2 `times` x
  5 -> x2 `times` x2 `times` x
  7 -> x2 `times` x2 `times` x2 `times` x

{-@ addRC :: xs: VecDSL F_BLS12 TF
          -> {ys:VecDSL F_BLS12 TF | vlength ys = vlength xs}
          -> {zs:VecDSL F_BLS12 TF | vlength zs = vlength xs} @-}
addRC :: DSL F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12
addRC = vZipWith TF TF TF plus

{-@ fullRound :: ins:Instance F_BLS12 -> VecDSL' F_BLS12 (t ins)
              -> VecDSL' F_BLS12 (t ins)
              -> VecDSL' F_BLS12 (t ins) @-}
fullRound :: Instance F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12
fullRound ins state rc = matMulExternal ins (sbox ins (addRC state rc))

{-@ tGT0 :: ins:Instance F_BLS12 -> {t ins > 0} @-}
tGT0 :: Instance F_BLS12 -> Proof
tGT0 Ins {} = ()

{-@ partialRound :: ins:Instance F_BLS12 -> VecDSL' F_BLS12 (t ins)
                 -> FieldDSL F_BLS12
                 -> VecDSL' F_BLS12 (t ins) @-}
partialRound :: Instance F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12
partialRound ins state@(CONS h ts) rc = matMulInternal ins
     (CONS (sbox_p ins (h `plus` rc)) ts)
partialRound ins (NIL _) _ = tGT0 ins ?? error "impossible since t > 0"


-- poseidon2^π permutation
{- permutation :: ins:Instance F_BLS12 -> VecDSL' F_BLS12 (t ins)
                -> VecDSL' F_BLS12 (t ins) @-}
{-@ permutation :: ins:Instance F_BLS12 -> VecDSL' F_BLS12 (t ins)
                -> VecDSL' F_BLS12 (t ins) @-}
permutation :: Instance F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12
permutation ins@(Ins {..}) xs = step4
  where
    step1 = matMulExternal ins xs
    step2 = fold'  t (fullRound ins)    step1 roundConstants_f1
    step3 = fold'' t (partialRound ins) step2 roundConstants_p
    step4 = fold'  t (fullRound ins)    step3 roundConstants_f2


-- Type annocated folds (TODO: check if these types can be inferred automatically)
-- maybe with the proper qualifiers

{- qualif MyEqLen( v : DSL @(0), x : int): ((x = (vlength v))) @-}
{- qualif MyEqLen2( v : DSL @(0), ins:Instance @(0)): ((t ins = (vlength v))) @-}
{- qualif MyTyped( v : DSL @(0)): ((DSL.typed v (DSL.TVec DSL.TF))) @-}
{- qualif MyTyped( v : DSL @(0)): ((DSL.typed v DSL.TF)) @-}


{-@ fold' :: n:Nat
          -> (VecDSL' F_BLS12 n -> VecDSL' F_BLS12 n -> VecDSL' F_BLS12 n)
          ->  VecDSL' F_BLS12 n -> [VecDSL' F_BLS12 n] ->  VecDSL' F_BLS12 n @-}
fold' :: Int -> (DSL F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12)
      -> DSL F_BLS12 -> [DSL F_BLS12] -> DSL F_BLS12
fold' _ _ z []     = z
fold' n f z (x:xs) = fold' n f (f z x) xs

{-@ fold'' :: n:Nat
          -> (VecDSL' F_BLS12 n -> FieldDSL F_BLS12 -> VecDSL' F_BLS12 n)
          ->  VecDSL' F_BLS12 n -> [FieldDSL F_BLS12] ->  VecDSL' F_BLS12 n @-}
fold'' :: Int -> (DSL F_BLS12 -> DSL F_BLS12 -> DSL F_BLS12)
       -> DSL F_BLS12 -> [DSL F_BLS12] -> DSL F_BLS12
fold'' _ _ z []     = z
fold'' n f z (x:xs) = fold'' n f (f z x) xs
