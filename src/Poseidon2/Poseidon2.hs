{-# LANGUAGE RecordWildCards, OrPatterns, ScopedTypeVariables #-}
{-@ LIQUID "--reflection" @-}
{- LIQUID "--eliminate=none" @-}
{-@ LIQUID "--ple" @-}
module Poseidon2.Poseidon2 where

import Utils
import DSL
import PlinkLib
import Semantics
import PlinkST
import Poseidon2.Poseidon2Cnst

import Language.Haskell.Liquid.ProofCombinators

{-@ vZipWithCost :: τ1:Ty -> τ2:Ty -> τ3:Ty
                 -> n:Nat
                 -> f:({a:DSL p | typed a τ1} -> {b:DSL p | typed b τ2} ->
                       {c:DSL p | typed c τ3 && ccost c = n + ccost a + ccost b})
                 -> xs:VecDSL p τ1 -> {ys:VecDSL p τ2 | vlength ys = vlength xs}
                 -> { ccost (vZipWith τ1 τ2 τ3 f xs ys) =
                      n*(vlength xs) + ccost xs + ccost ys } @-}
vZipWithCost :: Ty -> Ty -> Ty
             -> Int
             -> (DSL p -> DSL p -> DSL p)
             -> DSL p -> DSL p
             -> Proof
vZipWithCost _  _  _  _ _ (NIL _)     (NIL _)     = trivial
vZipWithCost τ1 τ2 τ3 n f (CONS x xs) (CONS y ys)
    = vZipWithCost τ1 τ2 τ3 n f xs ys ? ccost (f x y)


{-@ vSumCost :: xs:VecDSL p TF
             -> { ccost (vSum xs) = 1 + vlength xs + ccost xs } @-}
vSumCost :: Num p => DSL p -> Proof
vSumCost (NIL _) = trivial
vSumCost (CONS x xs) = vSumCost xs


{-@ mapCost :: m:Nat -> n:Nat
            -> f:(x:DSL p -> {y:DSL p | ccost y <= m*ccost x + n})
            -> xs:[DSL p]
            -> { ccosts (map' f xs) <= m*ccosts xs + n*(len xs) } @-}
mapCost :: Int -> Int -> (DSL p -> DSL p) -> [DSL p] -> Proof
mapCost m n f l@[] = trivial
mapCost m n f l@(x:xs)
  =   ccosts (map' f (x:xs))
  === ccosts (f x : map' f xs)
      ? mapCost m n f xs
  =<= (m*ccost x + n) + (m*ccosts xs + n*length xs)
  === m*(ccosts (x:xs)) + n*(length (x:xs))
  *** QED


{-@ matMulInternal :: ins:Instance p -> xs:VecDSL' p (t ins)
                   -> {v:VecDSL' p (t ins) | ccost v <=
                         ccost xs + (t ins)*(ccost xs + 4 + (t ins))} @-}
matMulInternal :: Num p => Instance p -> DSL p -> DSL p
matMulInternal ins@(Ins {..}) xs = case t of
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
  (4;8;12;16;20;24) ->
    vZipWithCost TF TF TF (ccost sum + 2) zipFn xs matInternalDiag
    ?? vZipWith TF TF TF zipFn xs matInternalDiag
    where
      {-@ sum :: {s:FieldDSL p | ccost s = (t ins) + 1 + ccost xs} @-}
      sum = vSum xs ? vSumCost xs

      {-@ zipFn :: x:FieldDSL p -> μ:FieldDSL p
                -> {v:FieldDSL p | ccost v = ccost sum + 2 + ccost x + ccost μ} @-}
      zipFn x μ = sum `plus` (μ `times` x)
  _ -> error "this value for t is not supported"


{-@ matMulExternal :: ins:Instance p -> xs:VecDSL' p (t ins)
                   -> {v:VecDSL' p (t ins) | ccost v <=
                         ccost xs + 2*(t ins)*(ccost xs + 4 + (t ins))} @-}
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

{-@ matMulM4' :: xs:{VecDSL p TF | (vlength xs) mod 4 = 0}
              -> {res:VecDSL p TF | vlength res = vlength xs
                    && ccost res <= ccost xs + 2*(vlength xs)*(ccost xs + 4 + (vlength xs))} @-}
matMulM4' :: forall p. Num p => DSL p -> DSL p
matMulM4' xs = vConcat TF step2 ? lengthsLemma 4 step2 where

  -- apply matMulM4 separately to each 4-element chunk:
  step1 = map' matMulM4 (vChunk TF 4 xs) ? mapCost 8 22 matMulM4 (vChunk TF 4 xs)
  step1 :: [DSL p]
  {-@ step1 :: {l:[VecDSL' p 4] | 4 * len l = vlength xs} @-}

  -- add components in four groups depending on their remainder modulo 4:
  sums = fold' 4 4 (2 * vlength xs) (vZipWith TF TF TF plus) (vReplicate TF 4 (CONST 0)) step1
  -- first 4 means it operates on 4-long lists
  -- second 4 means that each application of the function (vZipWith TF TF TF plus) introduces
  -- 4 new constraints
  -- 2 * vlength xs is because 8 new constraints are introduced for each 4-element
  -- chunk, of which there are vlength xs / 4

  sums :: DSL p
  {-@ sums :: VecDSL' p 4 @-}

  -- add the sums to each 4-element chunk:
  step2 = map' (vZipWith TF TF TF plus sums) step1
  step2 :: [DSL p]
  {-@ step2 :: {l:[VecDSL' p 4] | 4 * len l = vlength xs} @-}


{-@ matMulM4 :: xs:VecDSL' p 4
             -> {v:VecDSL' p 4 | ccost v <= 22 + 8*ccost xs} @-}
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
         -> PlinkST p (VecDSL' p (t ins)) @-}
sbox :: (Fractional p, Eq p) => Instance p -> DSL p -> PlinkST p (DSL p)
sbox ins = vMapM TF TF (sbox_p ins)

{-@ sbox_p :: Instance p -> FieldDSL p -> PlinkST p (FieldDSL p) @-}
sbox_p :: (Fractional p, Eq p) => Instance p -> DSL p -> PlinkST p (DSL p)
sbox_p (Ins {..}) x = yield res where
  x2 = (x `times` x)

  {-@ res :: FieldDSL p @-}
  res = case d of
    -- this parenthesization allows CSE to reuse some subexpressions
    3 -> x2 `times` x
    5 -> x2 `times` x2 `times` x
    7 -> x2 `times` x2 `times` x2 `times` x


{-@ addRC :: xs: VecDSL p TF
          -> {ys:VecDSL p TF | vlength ys = vlength xs}
          -> {zs:VecDSL p TF | vlength zs = vlength xs} @-}
addRC :: DSL p -> DSL p -> DSL p
addRC = vZipWith TF TF TF plus

{-@ fullRound :: ins:Instance p -> VecDSL' p (t ins)
              -> VecDSL' p (t ins)
              -> PlinkST p (VecDSL' p (t ins)) @-}
fullRound :: (Fractional p, Eq p)
          => Instance p -> DSL p -> DSL p -> PlinkST p (DSL p)
fullRound ins state rc = do
  nonLinear <- sbox ins (addRC state rc)
  let res = matMulExternal ins nonLinear
  yield res ? typed res (TVec TF)

{-@ tGT0 :: ins:Instance p -> {t ins > 0} @-}
tGT0 :: Instance p -> Proof
tGT0 Ins {} = ()

{-@ partialRound :: ins:Instance p -> VecDSL' p (t ins)
                 -> FieldDSL p
                 -> PlinkST p (VecDSL' p (t ins)) @-}
partialRound :: (Fractional p, Eq p)
             => Instance p -> DSL p -> DSL p -> PlinkST p (DSL p)
partialRound ins state@(CONS h ts) rc = do
  h' <- sbox_p ins (h `plus` rc)
  let res = matMulInternal ins (CONS h' ts)
  yield res ? typed res (TVec TF)
partialRound ins (NIL _) _ = tGT0 ins ?? error "impossible since t > 0"

-- poseidon2^π permutation
{- permutation :: ins:Instance p -> VecDSL' p (t ins)
                -> VecDSL' p (t ins) @-}
{-@ permutation :: ins:Instance p -> VecDSL' p (t ins)
                -> PlinkST p (VecDSL' p (t ins)) @-}
permutation :: (Fractional p, Eq p) => Instance p -> DSL p -> PlinkST p (DSL p)
permutation ins@(Ins {..}) xs = do
    let step1 = matMulExternal ins xs
    step2 <- foldM'  t (fullRound ins)    step1 roundConstants_f1
    step3 <- foldM'' t (partialRound ins) step2 roundConstants_p
    step4 <- foldM'  t (fullRound ins)    step3 roundConstants_f2

    return step4

{-@ fold' :: n:Nat -> m:Nat -> m2:Nat
          -> f:(x1:VecDSL' p n -> {x2:VecDSL' p n | ccost x2 <= m2} ->
                 {v:VecDSL' p n | ccost v <= ccost x1 + m + m2})
          -> z:VecDSL' p n
          -> xs:[{v:VecDSL' p n | ccost v <= m2}]
          -> {v:VecDSL' p n | ccost v <= ccost z + (m + m2) * (len xs)} @-}
fold' :: Int -> Int -> Int -> (DSL p -> DSL p -> DSL p) -> DSL p -> [DSL p] -> DSL p
fold' _ _ _  _ z []     = z
fold' n m m2 f z (x:xs) = fold' n m m2 f (f z x) xs

{-@ foldM' :: n:Nat
           -> (VecDSL' p n -> VecDSL' p n -> PlinkST p (VecDSL' p n))
           ->  VecDSL' p n -> [VecDSL' p n] -> PlinkST p (VecDSL' p n) @-}
foldM' :: Int -> (DSL p -> DSL p -> PlinkST p (DSL p))
      -> DSL p -> [DSL p] -> PlinkST p (DSL p)
foldM' _ _ z []     = pure z
foldM' n f z (x:xs) = do
  z' <- f z x
  foldM' n f z' xs

{-@ foldM'' :: n:Nat
            -> (VecDSL' p n -> FieldDSL p -> PlinkST p (VecDSL' p n))
            ->  VecDSL' p n -> [FieldDSL p] -> PlinkST p (VecDSL' p n) @-}
foldM'' :: Int -> (DSL p -> DSL p -> PlinkST p (DSL p))
       -> DSL p -> [DSL p] -> PlinkST p (DSL p)
foldM'' _ _ z []     = pure z
foldM'' n f z (x:xs) = do
  z' <- f z x
  foldM'' n f z' xs
