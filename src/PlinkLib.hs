{-# OPTIONS_GHC -Wno-missing-signatures -Wno-name-shadowing
                -fno-cse -fno-full-laziness #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix +++ @-}

module PlinkLib where

import DSL
import Utils (pow, map')

import GlobalStore

-- General functions for variables ---------------------------------------------
{-@ vecVar :: strs:[String] -> {v:DSL p [t] | vlength v = len strs} @-}
vecVar :: [String] -> DSL p [t]
vecVar strs = fromList (map' VAR strs)

-- List-like functions ---------------------------------------------------------
{-@ fromList :: l:[{v:DSL p t | scalar v}] ->
               {v:DSL p [t] | vector v && vlength v = len l} @-}
fromList :: [DSL p t] -> DSL p [t]
fromList []     = NIL
fromList (x:xs) = x `CONS` fromList xs

{-@ get :: v:{DSL p [t] | vector v} -> Btwn 0 (vlength v) -> DSL p t @-}
get :: DSL p [t] -> Int -> DSL p t
get (CONS p _ ) 0 = p
get (CONS _ ps) i = get ps (i-1)

{-@ set :: v:{DSL p [t] | vector v} -> Btwn 0 (vlength v) ->
           {x:DSL p t | scalar x} ->
           {u:DSL p [t] | vector u && vlength u = vlength v} @-}
set :: DSL p [t] -> Int -> DSL p t -> DSL p [t]
set (CONS _ ps) 0 x = CONS x ps
set (CONS p ps) i x = CONS p (set ps (i-1) x)

{-@ (+++) :: u:{DSL p [t] | vector u} ->
             v:{DSL p [t] | vector v} ->
             {w:DSL p [t] | vlength w = vlength u + vlength v} @-}
(+++) :: DSL p [t] -> DSL p [t] -> DSL p [t]
(NIL)       +++ ys = ys
(CONS x xs) +++ ys = CONS x (xs +++ ys)

infixr 5 +++

{-@ vConcat :: vs:[{u:DSL p [t] | vector u}]
            -> {v:DSL p [t] | vector v && vlength v = lengths vs} @-}
vConcat :: [DSL p [t]] -> DSL p [t]
vConcat ([])   = NIL
vConcat (p:ps) = p +++ vConcat ps

{-@ reflect lengths @-}
{-@ lengths :: [{v:DSL p [t] | vector v}] -> Nat @-}
lengths :: [DSL p [t]] -> Int
lengths [] = 0
lengths (p:ps) = vlength p + lengths ps

{-@ vTakeDrop :: n:Nat -> u:{DSL p [t] | vector u && vlength u >= n} ->
                ({v:DSL p [t] | vector v && vlength v = n},
                 {w:DSL p [t] | vector w && vlength w = (vlength u) - n}) @-}
vTakeDrop :: Int -> DSL p [t] -> (DSL p [t], DSL p [t])
vTakeDrop 0 xs          = (NIL, xs)
vTakeDrop n (CONS x xs) = let (ys, zs) = vTakeDrop (n-1) xs in (CONS x ys, zs)

{-@ vReplicate :: n:Nat -> {p:DSL p t | scalar p} ->
                  {v:DSL p [t] | vector v && vlength v = n} @-}
vReplicate :: Int -> DSL p t -> DSL p [t]
vReplicate 0 _ = NIL
vReplicate n p = CONS p (vReplicate (n-1) p)

{-@ vZip :: u:{DSL p [t] | vector u} ->
            v:{DSL p [t] | vector v && vlength v = vlength u} ->
            w:{[({x:DSL p t | scalar x},
                 {y:DSL p t | scalar y})] |
                 len w = vlength u} @-}
vZip :: DSL p [t] -> DSL p [t] -> [(DSL p t, DSL p t)]
vZip (NIL)       (NIL)       = []
vZip (CONS x xs) (CONS y ys) = (x,y) : vZip xs ys

{-@ vZipWith :: op:(DSL p t -> DSL p t -> DSL p t) ->
                u:{DSL p [t] | vector u} ->
                v:{DSL p [t] | vector v && vlength v = vlength u} ->
                w:{DSL p [t] | vector w && vlength w = vlength u} @-}
vZipWith :: (DSL p t -> DSL p t -> DSL p t)
         -> DSL p [t] -> DSL p [t] -> DSL p [t]
vZipWith _  (NIL)       (NIL)       = NIL
vZipWith op (CONS x xs) (CONS y ys) = op x y `CONS` vZipWith op xs ys

{-@ vMap :: op:(DSL p t -> DSL p t)
         -> u:{DSL p [t] | vector u}
         -> v:{DSL p [t] | vector v && vlength v = vlength u} @-}
vMap :: (DSL p t -> DSL p t) -> DSL p [t] -> DSL p [t]
vMap _  (NIL)       = NIL
vMap op (CONS x xs) = op x `CONS` vMap op xs

{-@ vChunk :: n:Nat1 -> v:{DSL p [t] | vector v && (vlength v) mod n = 0}
           -> {l:[{w:DSL p [t] | vector w && vlength w = n}]
                | n * len l = vlength v}
            / [vlength v] @-}
vChunk :: Int -> DSL p [t] -> [DSL p [t]]
vChunk _ NIL = []
vChunk n xs  = let (ys, zs) = vTakeDrop n xs in ys : (vChunk n zs)

-- Bitwise operations ----------------------------------------------------------
{-@ vNot :: u:{DSL p [Bool] | vector u} ->
            w:{DSL p [Bool] | vector w && vlength w = vlength u} @-}
vNot = vMap NOT

{-@ vAnd :: u:{DSL p [Bool] | vector u} ->
            v:{DSL p [Bool] | vector v && vlength v = vlength u} ->
            w:{DSL p [Bool] | vector w && vlength w = vlength u} @-}
vAnd = vZipWith AND

{-@ vOr :: u:{DSL p [Bool] | vector u} ->
           v:{DSL p [Bool] | vector v && vlength v = vlength u} ->
           w:{DSL p [Bool] | vector w && vlength w = vlength u} @-}
vOr = vZipWith OR

{-@ vXor :: u:{DSL p [Bool] | vector u} ->
            v:{DSL p [Bool] | vector v && vlength v = vlength u} ->
            w:{DSL p [Bool] | vector w && vlength w = vlength u} @-}
vXor = vZipWith XOR

-- Shift & rotate --------------------------------------------------------------
{-@ rotateL :: u:{DSL p [t] | vector u} -> Btwn 0 (vlength u) ->
               {v:DSL p [t] | vector v && vlength v = vlength u} @-}
rotateL :: DSL p [t] -> Int -> DSL p [t]
rotateL xs n = let (ys, zs) = vTakeDrop n xs in zs +++ ys

{-@ rotateR :: u:{DSL p [t] | vector u} -> Btwn 0 (vlength u) ->
               {v:DSL p [t] | vector v && vlength v = vlength u} @-}
rotateR :: DSL p [t] -> Int -> DSL p [t]
rotateR xs n = let (ys, zs) = vTakeDrop (vlength xs - n) xs in zs +++ ys

{-@ shiftL :: u:{DSL p [Bool] | vector u} -> Btwn 0 (vlength u) ->
              {v:DSL p [Bool] | vector v && vlength v = vlength u} @-}
shiftL :: Num p => DSL p [Bool] -> Int -> DSL p [Bool]
shiftL xs n = let (_, zs) = vTakeDrop n xs in
  zs +++ vReplicate n FALSE

{-@ shiftR :: u:{DSL p [Bool] | vector u} -> Btwn 0 (vlength u) ->
              {v:DSL p [Bool] | vector v && vlength v = vlength u} @-}
shiftR :: Num p => DSL p [Bool] -> Int -> DSL p [Bool]
shiftR xs n = let (ys, _) = vTakeDrop (vlength xs - n) xs in
  vReplicate n FALSE +++ ys

-- Integers mod 2^n -----------------------------------------------------------
{-@ fromInt :: n:Nat -> x:Btwn 0 (pow 2 n) ->
              {v:DSL p [Bool] | vector v && vlength v = n} @-}
fromInt :: Num p => Int -> Int -> DSL p [Bool]
fromInt n = go 0 NIL where
  {-@ go :: m:{Nat | m <= n} ->
            {acc:DSL p [Bool] | vector acc && vlength acc = m} ->
            x:Btwn 0 (pow 2 n) ->
            {v:DSL p [Bool] | vector v && vlength v = n} / [n-m] @-}
  go :: Num p => Int -> DSL p [Bool] -> Int -> DSL p [Bool]
  go m acc x
    | m == n    = acc
    | otherwise = let (q, r) = divMod x 2; r' = toDSLBool r
                  in go (m+1) (r' `CONS` acc) q


{-@ binaryValue :: {v:DSL p [Bool] | vector v && vlength v > 0}
                -> GlobalStore p (DSL p p) @-}
binaryValue :: (Integral p, Fractional p, Eq p) =>
               DSL p [Bool] -> GlobalStore p (DSL p p)
binaryValue v = go v (CONST 0) where
  {-@ go :: {v:DSL p [Bool] | vector v} -> acc:DSL p p
         -> GlobalStore p (DSL p p) @-}
  go :: (Integral p, Fractional p, Eq p) =>
        DSL p [Bool] -> DSL p p -> GlobalStore p (DSL p p)
  go NIL         acc = pure acc
  go (CONS x xs) acc = do
    let bit = var "bit" -- auxiliary variable to not grow programs exponentially
    define bit (eval x) -- hint for witness generation
    assert $ DEF bit x  -- constrain it to have the correct value
    assert $ BOOL (VAR bit)
    go xs (VAR bit `ADD` (acc `MUL` CONST 2))

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

{-@ fromBinary :: {v:DSL p [Bool] | vector v && vlength v > 0}
               -> GlobalStore p (DSL p p) @-}
fromBinary :: (Integral p, Fractional p, Eq p) =>
              DSL p [Bool] -> GlobalStore p (DSL p p)
fromBinary vec = do
  let x' = var "x"
  let x = VAR x'

  val <- binaryValue vec
  assert $ val `EQA` x
  define x' (eval val) -- evaluate `val` (value) to a field element
  return x

{-@ toBinary :: n:Nat1 -> DSL p p
             -> GlobalStore p ({v:DSL p [Bool] | vector v && vlength v = n}) @-}
toBinary :: (Integral p, Fractional p, Eq p) =>
            Int -> DSL p p -> GlobalStore p (DSL p [Bool])
toBinary n x = do
  let vec' = vars n "bits"
  let vec = vecVar vec'

  val <- binaryValue vec
  assert $ val `EQA` x
  defineVec vec' (\v -> binaryRepr n <$> eval x v)
  return vec


-- x + y (mod 2^e)
{-@ addMod :: Nat1
           -> DSL p p -> DSL p p
           -> GlobalStore p (DSL p p) @-}
addMod :: (Integral p, Fractional p, Ord p) =>
          Int -> DSL p p -> DSL p p -> GlobalStore p (DSL p p)
addMod e x y = do
  let modulus = 2^e
  let b = var "overflow"
  let z = var "sum"
  assert $ BOOL (VAR b)
  assert $ (x `ADD` y) `EQA` (VAR z `ADD` (VAR b `MUL` CONST modulus))

  _evidence <- toBinary e (VAR z) -- z can be encoded using ‘e’ bits

  define b (\v -> (\x y -> if x + y < modulus then 0 else 1)
                   <$> eval x v <*> eval y v)
  define z (\v -> (\x y -> (x + y) `mod` modulus)
                   <$> eval x v <*> eval y v)
  return (VAR z)
