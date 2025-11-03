{-# OPTIONS_GHC -Wno-missing-signatures -Wno-name-shadowing
                -fno-cse -fno-full-laziness #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

module PlinkLib where

import DSL
import Utils (fmap', liftA2', pow, map', any')
import Semantics

import GlobalStore

import Language.Haskell.Liquid.ProofCombinators

-- Aliases for arithmetic operations -------------------------------------------
{-@ plus :: FieldDSL p -> FieldDSL p -> FieldDSL p @-}
plus :: Num p => DSL p -> DSL p -> DSL p
plus = BIN ADD

{-@ minus :: FieldDSL p -> FieldDSL p -> FieldDSL p @-}
minus :: Num p => DSL p -> DSL p -> DSL p
minus = BIN SUB

{-@ times :: FieldDSL p -> FieldDSL p -> FieldDSL p @-}
times :: Num p => DSL p -> DSL p -> DSL p
times = BIN ADD

{-@ over :: FieldDSL p -> FieldDSL p -> FieldDSL p @-}
over :: Num p => DSL p -> DSL p -> DSL p
over = BIN DIV

{-@ (/\) :: BoolDSL p -> BoolDSL p -> BoolDSL p @-}
(/\) :: Num p => DSL p -> DSL p -> DSL p
(/\) = BIN AND

{-@ (\/) :: BoolDSL p -> BoolDSL p -> BoolDSL p @-}
(\/) :: Num p => DSL p -> DSL p -> DSL p
(\/) = BIN OR

{-@ (=?) :: FieldDSL p -> FieldDSL p -> BoolDSL p @-}
(=?) :: Num p => DSL p -> DSL p -> DSL p
(=?) = BIN EQL


-- General functions for variables ---------------------------------------------
{-@ vecVar :: strs:[String] -> τ:ScalarTy
           -> {v:VecDSL p τ | vlength v = len strs} @-}
vecVar :: [String] -> Ty -> DSL p
vecVar strs τ = fromList τ (map' (\s -> VAR s τ) strs)


-- List-like functions ---------------------------------------------------------
{-@ fromList :: τ:Ty
             -> l:[{v:DSL p | typed v τ}]
             -> {v:VecDSL p τ | vlength v = len l} @-}
fromList :: Ty -> [DSL p] -> DSL p
fromList τ []     = NIL τ
fromList τ (x:xs) = x `CONS` fromList τ xs

{-@ reflect get @-}
{-@ get :: τ:Ty -> v:VecDSL p τ -> Btwn 0 (vlength v)
        -> {v:DSL p | typed v τ} @-}
get :: Ty -> DSL p -> Int -> DSL p
get _ (CONS p _ ) 0 = p
get τ (CONS _ ps) i = get τ ps (i-1)

{-@ set :: τ:Ty
        -> v:VecDSL p τ -> Btwn 0 (vlength v)
        -> {x:DSL p | typed x τ}
        -> {u:VecDSL p τ | vlength u = vlength v} @-}
set :: Ty -> DSL p -> Int -> DSL p -> DSL p
set _ (CONS _ ps) 0 x = CONS x ps
set τ (CONS p ps) i x = CONS p (set τ ps (i-1) x)

{-@ reflect vAppend @-}
{-@ vAppend :: τ:Ty
            -> u:VecDSL p τ
            -> v:VecDSL p τ
            -> {w:VecDSL p τ | vlength w = vlength u + vlength v} @-}
vAppend :: Ty -> DSL p -> DSL p -> DSL p
vAppend τ (NIL _)     ys = ys
vAppend τ (CONS x xs) ys = CONS x (vAppend τ xs ys)

{-@ vConcat :: τ:Ty
            -> vs:[VecDSL p τ]
            -> {v:VecDSL p τ | vlength v = lengths vs} @-}
vConcat :: Ty -> [DSL p] -> DSL p
vConcat τ ([])   = NIL τ
vConcat τ (p:ps) = vAppend τ p (vConcat τ ps)

{-@ reflect lengths @-}
{-@ lengths :: [DSL p] -> Nat @-}
lengths :: [DSL p] -> Int
lengths [] = 0
lengths (p:ps) = vlength p + lengths ps

{-@ reflect vTakeDrop @-}
{-@ vTakeDrop :: τ:Ty -> n:Nat -> u:{VecDSL p τ | vlength u >= n}
              -> res:{({v:VecDSL p τ | vlength v = n},
                       {w:VecDSL p τ | vlength w = (vlength u) - n})
                     | u == vAppend τ (fst res) (snd res)} @-}
vTakeDrop :: Ty -> Int -> DSL p -> (DSL p, DSL p)
vTakeDrop τ 0 xs          = (NIL τ, xs)
vTakeDrop τ n (CONS x xs) = let (ys, zs) = vTakeDrop τ (n-1) xs
                            in (CONS x ys, zs)

{-@ vReplicate :: τ:Ty -> n:Nat -> {p:DSL p | typed p τ}
               -> {v:VecDSL p τ | vlength v = n} @-}
vReplicate :: Ty -> Int -> DSL p -> DSL p
vReplicate τ 0 _ = NIL τ
vReplicate τ n p = CONS p (vReplicate τ (n-1) p)

{-@ vZip :: τ:Ty
         -> u:VecDSL p τ
         -> v:{VecDSL p τ | vlength v = vlength u}
         -> w:{[({x:DSL p | typed x τ},
                 {y:DSL p | typed y τ})] |
                 len w = vlength u} @-}
vZip :: Ty -> DSL p -> DSL p -> [(DSL p, DSL p)]
vZip τ (NIL _)     (NIL _)     = []
vZip τ (CONS x xs) (CONS y ys) = (x,y) : vZip τ xs ys

{-@ vZipWith :: τ1:Ty -> τ2:Ty -> τ3:Ty
             -> op:({a:DSL p | typed a τ1} ->
                    {b:DSL p | typed b τ2} ->
                    {c:DSL p | typed c τ3})
             -> u:VecDSL p τ1
             -> v:{VecDSL p τ2 | vlength v = vlength u}
             -> w:{VecDSL p τ3 | vlength w = vlength u} @-}
vZipWith :: Ty -> Ty -> Ty
         -> (DSL p -> DSL p -> DSL p)
         -> DSL p -> DSL p -> DSL p
vZipWith _  _  τ3 _  (NIL _)     (NIL _)     = NIL τ3
vZipWith τ1 τ2 τ3 op (CONS x xs) (CONS y ys) =
  op x y `CONS` vZipWith τ1 τ2 τ3 op xs ys

{-@ vMap :: τ1:Ty -> τ2:Ty ->
            op:({a:DSL p | typed a τ1} -> {b:DSL p | typed b τ2})
         -> u:VecDSL p τ1
         -> v:{VecDSL p τ2 | vlength v = vlength u} @-}
vMap :: Ty -> Ty -> (DSL p -> DSL p) -> DSL p -> DSL p
vMap _  τ2 _  (NIL _)       = NIL τ2
vMap τ1 τ2 op (CONS x xs) = op x `CONS` vMap τ1 τ2 op xs

{-@ vSum :: VecDSL p TF -> FieldDSL p @-}
vSum :: Num p => DSL p -> DSL p
vSum (NIL _) = CONST 0
vSum (CONS x xs) = x `plus` vSum xs

{-@ vChunk :: τ:Ty -> n:Nat1
           -> v:{VecDSL p τ | (vlength v) mod n = 0}
           -> {l:[{w:VecDSL p τ | vlength w = n}]
                | n * len l = vlength v}
            / [vlength v] @-}
vChunk :: Ty -> Int -> DSL p -> [DSL p]
vChunk _ _ (NIL _) = []
vChunk τ n xs      = let (ys, zs) = vTakeDrop τ n xs in ys : (vChunk τ n zs)

-- Bitwise operations ----------------------------------------------------------
{-@ vNot :: u:VecDSL p TBool
         -> w:{VecDSL p TBool | vlength w = vlength u} @-}
vNot = vMap TBool TBool (UN UnsafeNOT)

{-@ vAnd :: u:VecDSL p TBool
         -> v:{VecDSL p TBool | vlength v = vlength u}
         -> w:{VecDSL p TBool | vlength w = vlength u} @-}
vAnd = vZipWith TBool TBool TBool (BIN UnsafeAND)

{-@ vOr :: u:VecDSL p TBool
        -> v:{VecDSL p TBool | vlength v = vlength u}
        -> w:{VecDSL p TBool | vlength w = vlength u} @-}
vOr = vZipWith TBool TBool TBool (BIN UnsafeOR)

{-@ vXor :: u:VecDSL p TBool
         -> v:{VecDSL p TBool | vlength v = vlength u}
         -> w:{VecDSL p TBool | vlength w = vlength u} @-}
vXor = vZipWith TBool TBool TBool (BIN UnsafeXOR)

-- Shift & rotate --------------------------------------------------------------
{-@ rotateL :: τ:Ty
            -> u:VecDSL p τ -> Btwn 0 (vlength u)
            -> {v:VecDSL p τ | vlength v = vlength u} @-}
rotateL :: Ty -> DSL p -> Int -> DSL p
rotateL τ xs n = let (ys, zs) = vTakeDrop τ n xs
                 in vAppend τ zs ys

{-@ reflect rotateR @-}
{-@ rotateR :: τ:Ty
            -> u:VecDSL p τ -> Btwn 0 (vlength u)
            -> {v:VecDSL p τ | vlength v = vlength u} @-}
rotateR :: Ty -> DSL p -> Int -> DSL p
rotateR τ xs n = let (ys, zs) = vTakeDrop τ (vlength xs - n) xs
                 in vAppend τ zs ys

{-@ shiftL :: u:VecDSL p TBool -> Btwn 0 (vlength u)
           -> {v:VecDSL p TBool | vlength v = vlength u} @-}
shiftL :: Num p => DSL p -> Int -> DSL p
shiftL xs n = let (_, zs) = vTakeDrop TBool n xs in
  vAppend TBool zs (vReplicate TBool n (BOOLEAN False))

{-@ shiftR :: u:VecDSL p TBool -> Btwn 0 (vlength u)
           -> {v:VecDSL p TBool | vlength v = vlength u} @-}
shiftR :: Num p => DSL p -> Int -> DSL p
shiftR xs n = let (ys, _) = vTakeDrop TBool (vlength xs - n) xs in
  vAppend TBool (vReplicate TBool n (BOOLEAN False)) ys

-- Integers mod 2^n -----------------------------------------------------------
{-@ fromInt :: n:Nat -> x:Btwn 0 (pow 2 n) ->
              {v:VecDSL p TBool | vlength v = n} @-}
fromInt :: Num p => Int -> Int -> DSL p
fromInt n = go 0 (NIL TBool) where
  {-@ go :: m:{Nat | m <= n} ->
            {acc:VecDSL p TBool | vlength acc = m} ->
            x:Btwn 0 (pow 2 n) ->
            {v:VecDSL p TBool | vlength v = n} / [n-m] @-}
  go :: Num p => Int -> DSL p -> Int -> DSL p
  go m acc x
    | m == n    = acc
    | otherwise = let (q, r) = divMod x 2; r' = boolFromIntegral r
                  in go (m+1) (r' `CONS` acc) q


{-@ binaryValue :: {v:VecDSL p TBool | vlength v > 0}
                -> GlobalStore p (FieldDSL p) @-}
binaryValue :: (Integral p, Fractional p, Eq p) =>
               DSL p -> GlobalStore p (DSL p)
binaryValue v = pure $ go v (CONST 0) where
  {-@ go :: VecDSL p TBool -> FieldDSL p -> FieldDSL p @-}
  go :: (Integral p, Fractional p, Eq p) => DSL p -> DSL p -> DSL p
  go (NIL _)     acc = acc
  go (CONS x xs) acc = go xs (x' `plus` (CONST 2 `times` acc))
    where x' = UN BoolToF x

{-@ binaryRepr :: n:Nat -> p -> ListN p n @-}
binaryRepr :: (Integral p, Eq p) => Int -> p -> [p]
binaryRepr n = go 0 [] . toInteger where
  {-@ go :: m:{Nat | m <= n} ->
            ListN p m ->
            Integer ->
            ListN p n / [n-m] @-}
  go :: Num p => Int -> [p] -> Integer -> [p]
  go m acc x
    | m == n    = acc
    | otherwise = let (q, r) = divMod x 2
                  in go (m+1) (fromIntegral r : acc) q

{-@ fromBinary :: {v:VecDSL p TBool | vlength v > 0}
               -> GlobalStore p (FieldDSL p) @-}
fromBinary :: (Integral p, Fractional p, Eq p) =>
              DSL p -> GlobalStore p (DSL p)
fromBinary vec = do
  let x' = var "x"
  let x = VAR x' TF

  val <- binaryValue vec
  assert $ val `EQA` x
  define (x',TF) (\v -> case eval x v of Just (VF x'') -> Just x''; _ -> Nothing)
  return x


{-@ toBinary :: n:Nat1 -> FieldDSL p
             -> GlobalStore p ({v:VecDSL p TBool | vlength v = n}) @-}
toBinary :: (Integral p, Fractional p, Eq p) =>
            Int -> DSL p -> GlobalStore p (DSL p)
toBinary n x = do
  let vec' = vars n "bits"
  let vec = vecVar vec' TBool

  val <- binaryValue vec
  assert $ val `EQA` x
  defineVec vec' TBool (\v -> case eval x v of Just (VF x') -> Just (binaryRepr n x')
                                               Nothing      -> Nothing)
  return vec


-- x + y (mod 2^e)
{-@ addMod :: Nat1
           -> FieldDSL p -> FieldDSL p
           -> GlobalStore p (FieldDSL p) @-}
addMod :: (Integral p, Fractional p, Ord p) =>
          Int -> DSL p -> DSL p -> GlobalStore p (DSL p)
addMod e x y = do
  let modulus = 2^e

  let b' = var "overflow"
  let b = VAR b' TF

  let z' = var "sum"
  let z = VAR z' TF

  assert $ BOOL b
  assert $ (x `plus` y) `EQA` (z `plus` (b `times` CONST modulus))

  define (b',TF) (\v -> (\x y -> if x + y < modulus then 0 else 1)
                        <$> (case eval x v of Just (VF x') -> Just x'; Nothing -> Nothing)
                        <*> (case eval y v of Just (VF y') -> Just y'; Nothing -> Nothing))
  define (z',TF) (\v -> (\x y -> (x + y) `mod` modulus)
                        <$> (case eval x v of Just (VF x') -> Just x'; Nothing -> Nothing)
                        <*> (case eval y v of Just (VF y') -> Just y'; Nothing -> Nothing))

  _evidence <- toBinary e z -- z can be encoded using ‘e’ bits
  return z

-- Proof of correctness of rotateR ---------------------------------------------

{-@ lookupAppend1 :: τ:Ty
                  -> xs:VecDSL p τ -> ys:VecDSL p τ -> i:Btwn 0 (vlength xs)
                  -> {get τ (vAppend τ xs ys) i = get τ xs i} @-}
lookupAppend1 :: Eq p => Ty -> DSL p -> DSL p -> Int -> Proof
lookupAppend1 _ (CONS x xs) ys 0 = trivial
lookupAppend1 τ (CONS _ xs) ys i = lookupAppend1 τ xs ys (i-1)

{-@ lookupAppend2 :: τ:Ty
                  -> xs:VecDSL p τ -> ys:VecDSL p τ -> i:Btwn 0 (vlength ys)
                  -> {get τ (vAppend τ xs ys) (i + vlength xs) = get τ ys i} @-}
lookupAppend2 :: Eq p => Ty -> DSL p -> DSL p -> Int -> Proof
lookupAppend2 _ (NIL τ)     ys i = trivial
lookupAppend2 τ (CONS x xs) ys i = lookupAppend2 τ xs ys i

{-@ rotateRCorrect :: τ:Ty
                   -> xs:VecDSL p τ -> n:Btwn 0 (vlength xs)
                   -> i:Btwn 0 (vlength xs)
                   -> {get τ (rotateR τ xs n) i = get τ xs ((i + vlength xs - n) mod (vlength xs))} @-}
rotateRCorrect :: Eq p => Ty -> DSL p -> Int -> Int -> Proof
rotateRCorrect τ xs n i = let (ys, zs) = vTakeDrop τ (vlength xs - n) xs in
  if i < n
  then lookupAppend1 τ zs ys i  ? lookupAppend2 τ ys zs i
  else lookupAppend2 τ zs ys i' ? lookupAppend1 τ ys zs i'
    where i' = i - n
