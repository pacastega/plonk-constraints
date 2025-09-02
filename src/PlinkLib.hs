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

-- Aliases for arithmetic operations -------------------------------------------
{-@ plus :: {x:DSL p | typed x TF} -> {y:DSL p | typed y TF}
         -> {z:DSL p | typed z TF} @-}
plus :: Num p => DSL p -> DSL p -> DSL p
plus = BIN ADD

{-@ times :: {x:DSL p | typed x TF} -> {y:DSL p | typed y TF}
          -> {z:DSL p | typed z TF} @-}
times :: Num p => DSL p -> DSL p -> DSL p
times = BIN ADD

-- General functions for variables ---------------------------------------------
{-@ vecVar :: strs:[String] -> τ:ScalarTy
           -> {v:DSL p | typed v (TVec τ (len strs)) && vlength v = len strs} @-}
vecVar :: [String] -> Ty -> DSL p
vecVar strs τ = fromList τ (map' (\s -> VAR s τ) strs)

{-@ lazy expandVecVar @-}
{-@ expandVecVar :: vVar:{DSL p | isVar vVar && vector vVar}
                 -> {v:DSL p | vlength v = vlength vVar} @-}
expandVecVar :: DSL p -> DSL p
expandVecVar (VAR name (TVec τ n)) = fromList τ variables where
  varNames = vars n name -- n "fresh" copies of name
  variables = case τ of
    TVec {} -> map (expandVecVar . mkVar) varNames
    _       -> map mkVar                  varNames
  mkVar s = VAR s τ


-- List-like functions ---------------------------------------------------------
{-@ type PlinkVec p T = {v:DSL p | typed v (TVec T (vlength v))} @-}

{-@ fromList :: τ:Ty
             -> l:[{v:DSL p | typed v τ}]
             -> {v:DSL p | typed v (TVec τ (len l)) && vlength v = len l} @-}
fromList :: Ty -> [DSL p] -> DSL p
fromList τ []     = NIL τ
fromList τ (x:xs) = x `CONS` fromList τ xs

{-@ get :: τ:Ty -> v:PlinkVec p τ -> Btwn 0 (vlength v)
        -> {v:DSL p | typed v τ} @-}
get :: Ty -> DSL p -> Int -> DSL p
get _ (CONS p _ ) 0 = p
get τ (CONS _ ps) i = get τ ps (i-1)

{-@ set :: τ:Ty
        -> v:PlinkVec p τ -> Btwn 0 (vlength v)
        -> {x:DSL p | typed x τ}
        -> {u:PlinkVec p τ | vlength u = vlength v} @-}
set :: Ty -> DSL p -> Int -> DSL p -> DSL p
set _ (CONS _ ps) 0 x = CONS x ps
set τ (CONS p ps) i x = CONS p (set τ ps (i-1) x)

{-@ vAppend :: τ:Ty
            -> u:PlinkVec p τ
            -> v:PlinkVec p τ
            -> {w:PlinkVec p τ | vlength w = vlength u + vlength v} @-}
vAppend :: Ty -> DSL p -> DSL p -> DSL p
vAppend τ (NIL _)     ys = ys
vAppend τ (CONS x xs) ys = CONS x (vAppend τ xs ys)

{-@ vConcat :: τ:Ty
            -> vs:[PlinkVec p τ]
            -> {v:PlinkVec p τ | vlength v = lengths vs} @-}
vConcat :: Ty -> [DSL p] -> DSL p
vConcat τ ([])   = NIL τ
vConcat τ (p:ps) = vAppend τ p (vConcat τ ps)

{-@ reflect lengths @-}
{-@ lengths :: [DSL p] -> Nat @-}
lengths :: [DSL p] -> Int
lengths [] = 0
lengths (p:ps) = vlength p + lengths ps

{-@ vTakeDrop :: τ:Ty -> n:Nat -> u:{PlinkVec p τ | vlength u >= n}
              -> ({v:DSL p | typed v (TVec τ n) && vlength v = n},
                  {w:DSL p | typed w (TVec τ ((vlength u) - n))
                          && vlength w = (vlength u) - n})
@-}
vTakeDrop :: Ty -> Int -> DSL p -> (DSL p, DSL p)
vTakeDrop τ 0 xs          = (NIL τ, xs)
vTakeDrop τ n (CONS x xs) = let (ys, zs) = vTakeDrop τ (n-1) xs
                            in (CONS x ys, zs)

{-@ vReplicate :: τ:Ty -> n:Nat -> {p:DSL p | typed p τ}
               -> {v:DSL p | typed v (TVec τ n) && vlength v = n} @-}
vReplicate :: Ty -> Int -> DSL p -> DSL p
vReplicate τ 0 _ = NIL τ
vReplicate τ n p = CONS p (vReplicate τ (n-1) p)

{-@ vZip :: τ:Ty
         -> u:PlinkVec p τ
         -> v:{PlinkVec p τ | vlength v = vlength u}
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
             -> u:PlinkVec p τ1
             -> v:{PlinkVec p τ2 | vlength v = vlength u}
             -> w:{PlinkVec p τ3 | vlength w = vlength u} @-}
vZipWith :: Ty -> Ty -> Ty
         -> (DSL p -> DSL p -> DSL p)
         -> DSL p -> DSL p -> DSL p
vZipWith _  _  τ3 _  (NIL _)     (NIL _)     = NIL τ3
vZipWith τ1 τ2 τ3 op (CONS x xs) (CONS y ys) =
  op x y `CONS` vZipWith τ1 τ2 τ3 op xs ys

{-@ vMap :: τ1:Ty -> τ2:Ty ->
            op:({a:DSL p | typed a τ1} -> {b:DSL p | typed b τ2})
         -> u:PlinkVec p τ1
         -> v:{PlinkVec p τ2 | vlength v = vlength u} @-}
vMap :: Ty -> Ty -> (DSL p -> DSL p) -> DSL p -> DSL p
vMap _  τ2 _  (NIL _)       = NIL τ2
vMap τ1 τ2 op (CONS x xs) = op x `CONS` vMap τ1 τ2 op xs

{-@ vChunk :: τ:Ty -> n:Nat1
           -> v:{PlinkVec p τ | (vlength v) mod n = 0}
           -> {l:[{w:DSL p | typed w (TVec τ n) && vlength w = n}]
                | n * len l = vlength v}
            / [vlength v] @-}
vChunk :: Ty -> Int -> DSL p -> [DSL p]
vChunk _ _ (NIL _) = []
vChunk τ n xs      = let (ys, zs) = vTakeDrop τ n xs in ys : (vChunk τ n zs)

-- Bitwise operations ----------------------------------------------------------
{-@ vNot :: u:PlinkVec p TBool
         -> w:{PlinkVec p TBool | vlength w = vlength u} @-}
vNot = vMap TBool TBool (UN UnsafeNOT)

{-@ vAnd :: u:PlinkVec p TBool
         -> v:{PlinkVec p TBool | vlength v = vlength u}
         -> w:{PlinkVec p TBool | vlength w = vlength u} @-}
vAnd = vZipWith TBool TBool TBool (BIN UnsafeAND)

{-@ vOr :: u:PlinkVec p TBool
        -> v:{PlinkVec p TBool | vlength v = vlength u}
        -> w:{PlinkVec p TBool | vlength w = vlength u} @-}
vOr = vZipWith TBool TBool TBool (BIN UnsafeOR)

{-@ vXor :: u:PlinkVec p TBool
        -> v:{PlinkVec p TBool | vlength v = vlength u}
        -> w:{PlinkVec p TBool | vlength w = vlength u} @-}
vXor = vZipWith TBool TBool TBool (BIN UnsafeXOR)

-- Shift & rotate --------------------------------------------------------------
{-@ rotateL :: τ:Ty
            -> u:PlinkVec p τ -> Btwn 0 (vlength u)
            -> {v:PlinkVec p τ | vlength v = vlength u} @-}
rotateL :: Ty -> DSL p -> Int -> DSL p
rotateL τ xs n = let (ys, zs) = vTakeDrop τ n xs
                 in vAppend τ zs ys

{-@ rotateR :: τ:Ty
            -> u:PlinkVec p τ -> Btwn 0 (vlength u)
            -> {v:PlinkVec p τ | vlength v = vlength u} @-}
rotateR :: Ty -> DSL p -> Int -> DSL p
rotateR τ xs n = let (ys, zs) = vTakeDrop τ (vlength xs - n) xs
                 in vAppend τ zs ys

{-@ shiftL :: u:PlinkVec p TBool -> Btwn 0 (vlength u)
           -> {v:PlinkVec p TBool | vlength v = vlength u} @-}
shiftL :: Num p => DSL p -> Int -> DSL p
shiftL xs n = let (_, zs) = vTakeDrop TBool n xs in
  vAppend TBool zs (vReplicate TBool n (BOOLEAN False))

{-@ shiftR :: u:PlinkVec p TBool -> Btwn 0 (vlength u)
           -> {v:PlinkVec p TBool | vlength v = vlength u} @-}
shiftR :: Num p => DSL p -> Int -> DSL p
shiftR xs n = let (ys, _) = vTakeDrop TBool (vlength xs - n) xs in
  vAppend TBool (vReplicate TBool n (BOOLEAN False)) ys

-- Integers mod 2^n -----------------------------------------------------------
{-@ fromInt :: n:Nat -> x:Btwn 0 (pow 2 n) ->
              {v:DSL p | typed v (TVec TBool n) && vlength v = n} @-}
fromInt :: Num p => Int -> Int -> DSL p
fromInt n = go 0 (NIL TBool) where
  {-@ go :: m:{Nat | m <= n} ->
            {acc:DSL p | typed acc (TVec TBool m) && vlength acc = m} ->
            x:Btwn 0 (pow 2 n) ->
            {v:DSL p | typed v (TVec TBool n) && vlength v = n} / [n-m] @-}
  go :: Num p => Int -> DSL p -> Int -> DSL p
  go m acc x
    | m == n    = acc
    | otherwise = let (q, r) = divMod x 2; r' = boolFromIntegral r
                  in go (m+1) (r' `CONS` acc) q


{-@ binaryValue :: {v:PlinkVec p TBool | vlength v > 0}
                -> GlobalStore p ({d:DSL p | typed d TF}) @-}
binaryValue :: (Integral p, Fractional p, Eq p) =>
               DSL p -> GlobalStore p (DSL p)
binaryValue v = pure $ go v (CONST 0) where
  {-@ go :: PlinkVec p TBool -> {acc:DSL p | typed acc TF}
         -> ({d:DSL p | typed d TF}) @-}
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

{-@ fromBinary :: {v:PlinkVec p TBool | vlength v > 0}
               -> GlobalStore p ({d:DSL p | typed d TF}) @-}
fromBinary :: (Integral p, Fractional p, Eq p) =>
              DSL p -> GlobalStore p (DSL p)
fromBinary vec = do
  let x' = var "x"
  let x = VAR x' TF

  val <- binaryValue vec
  assert $ val `EQA` x
  define x' (\v -> case eval x v of Just (VF x'') -> Just x''; _ -> Nothing)
  return x


{-@ toBinary :: n:Nat1 -> {d:DSL p | typed d TF}
             -> GlobalStore p ({v:DSL p | typed v (TVec TBool n)
                                       && vlength v = n}) @-}
toBinary :: (Integral p, Fractional p, Eq p) =>
            Int -> DSL p -> GlobalStore p (DSL p)
toBinary n x = do
  let vec' = vars n "bits"
  let vec = vecVar vec' TBool

  val <- binaryValue vec
  assert $ val `EQA` x
  defineVec vec' (\v -> case eval x v of Just (VF x') -> Just (binaryRepr n x')
                                         Nothing      -> Nothing)
  return vec


-- x + y (mod 2^e)
{-@ addMod :: Nat1
           -> {x:DSL p | typed x TF} -> {y:DSL p | typed y TF}
           -> GlobalStore p ({z:DSL p | typed z TF}) @-}
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

  define b' (\v -> (\x y -> if x + y < modulus then 0 else 1)
                   <$> (case eval x v of Just (VF x') -> Just x'; Nothing -> Nothing)
                   <*> (case eval y v of Just (VF y') -> Just y'; Nothing -> Nothing))
  define z' (\v -> (\x y -> (x + y) `mod` modulus)
                   <$> (case eval x v of Just (VF x') -> Just x'; Nothing -> Nothing)
                   <*> (case eval y v of Just (VF y') -> Just y'; Nothing -> Nothing))

  _evidence <- toBinary e z -- z can be encoded using ‘e’ bits
  return z
