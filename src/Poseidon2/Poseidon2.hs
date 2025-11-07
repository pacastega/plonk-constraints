{-# LANGUAGE RecordWildCards, OrPatterns, ScopedTypeVariables #-}
{-@ LIQUID "--reflection" @-}
{- LIQUID "--eliminate=none" @-}
{-@ LIQUID "--ple" @-}
module Poseidon2.Poseidon2 where

import Utils
import DSL
import PlinkLib
import Poseidon2.Poseidon2Cnst

import Language.Haskell.Liquid.ProofCombinators

{-@ matMulInternal :: ins:Instance p -> VecDSL' p (t ins)
                   -> VecDSL' p (t ins) @-}
matMulInternal :: Num p => Instance p -> DSL p -> DSL p
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

{-@ matMulExternal :: ins:Instance p -> VecDSL' p (t ins)
                   -> VecDSL' p (t ins) @-}
matMulExternal :: Num p => Instance p -> DSL p -> DSL p
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

{-@ matMulM4' :: {v:VecDSL p TF | (vlength v) mod 4 = 0}
              -> {res:VecDSL p TF | vlength res = vlength v} @-}
matMulM4' :: forall p. Num p => DSL p -> DSL p
matMulM4' xs = vConcat TF step2 ? lengthsLemma 4 step2 where

  -- apply matMulM4 separately to each 4-element chunk:
  step1 = map matMulM4 (vChunk TF 4 xs)
  step1 :: Num p => [DSL p]
  {-@ step1 :: {l:[VecDSL' p 4] | 4 * len l = vlength xs} @-}

  -- add components in four groups depending on their remainder modulo 4:
  sums = fold' 4 (vZipWith TF TF TF plus) (vReplicate TF 4 (CONST 0)) step1
  sums :: Num p => DSL p
  {-@ sums :: VecDSL' p 4 @-}

  -- add the sums to each 4-element chunk:
  step2 = map (vZipWith TF TF TF plus sums) step1
  step2 :: Num p => [DSL p]
  {-@ step2 :: {l:[VecDSL' p 4] | 4 * len l = vlength xs} @-}


{-@ matMulM4 :: VecDSL' p 4 -> VecDSL' p 4 @-}
matMulM4 :: Num p => DSL p -> DSL p
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
          {-@ t0 :: FieldDSL p @-}
          {-@ t1 :: FieldDSL p @-}
          {-@ t2 :: FieldDSL p @-}
          {-@ t3 :: FieldDSL p @-}
          {-@ t4 :: FieldDSL p @-}
          {-@ t5 :: FieldDSL p @-}
          {-@ t6 :: FieldDSL p @-}
          {-@ t7 :: FieldDSL p @-}


{-@ sbox :: ins:Instance p -> VecDSL' p (t ins)
         -> VecDSL' p (t ins) @-}
sbox :: Num p => Instance p -> DSL p -> DSL p
sbox ins = vMap TF TF (sbox_p ins)

{-@ sbox_p :: Instance p -> FieldDSL p -> FieldDSL p @-}
sbox_p :: Num p => Instance p -> DSL p -> DSL p
sbox_p (Ins {..}) x = let x2 = (x `times` x) in case d of
  -- this parenthesization allows CSE to reuse some subexpressions
  3 -> x2 `times` x
  5 -> x2 `times` x2 `times` x
  7 -> x2 `times` x2 `times` x2 `times` x

{-@ addRC :: xs: VecDSL p TF
          -> {ys:VecDSL p TF | vlength ys = vlength xs}
          -> {zs:VecDSL p TF | vlength zs = vlength xs} @-}
addRC :: Num p => DSL p -> DSL p -> DSL p
addRC = vZipWith TF TF TF plus

{-@ fullRound :: ins:Instance p -> VecDSL' p (t ins)
              -> VecDSL' p (t ins)
              -> VecDSL' p (t ins) @-}
fullRound :: Num p => Instance p -> DSL p -> DSL p -> DSL p
fullRound ins state rc = matMulExternal ins (sbox ins (addRC state rc))

{-@ tGT0 :: ins:Instance p -> {t ins > 0} @-}
tGT0 :: Instance p -> Proof
tGT0 Ins {} = ()

{-@ partialRound :: ins:Instance p -> VecDSL' p (t ins)
                 -> FieldDSL p
                 -> VecDSL' p (t ins) @-}
partialRound :: Num p => Instance p -> DSL p -> DSL p -> DSL p
partialRound ins state@(CONS h ts) rc = matMulInternal ins
     (CONS (sbox_p ins (h `plus` rc)) ts)
partialRound ins (NIL _) _ = tGT0 ins ?? error "impossible since t > 0"


-- poseidon2^π permutation
{- permutation :: ins:Instance p -> VecDSL' p (t ins)
                -> VecDSL' p (t ins) @-}
{-@ permutation :: ins:Instance p -> VecDSL' p (t ins)
                -> VecDSL' p (t ins) @-}
permutation :: Num p => Instance p -> DSL p -> DSL p
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
          -> (VecDSL' p n -> VecDSL' p n -> VecDSL' p n)
          ->  VecDSL' p n -> [VecDSL' p n] ->  VecDSL' p n @-}
fold' :: Int -> (DSL p -> DSL p -> DSL p)
      -> DSL p -> [DSL p] -> DSL p
fold' _ _ z []     = z
fold' n f z (x:xs) = fold' n f (f z x) xs

{-@ fold'' :: n:Nat
          -> (VecDSL' p n -> FieldDSL p -> VecDSL' p n)
          ->  VecDSL' p n -> [FieldDSL p] ->  VecDSL' p n @-}
fold'' :: Int -> (DSL p -> DSL p -> DSL p)
       -> DSL p -> [DSL p] -> DSL p
fold'' _ _ z []     = z
fold'' n f z (x:xs) = fold'' n f (f z x) xs
