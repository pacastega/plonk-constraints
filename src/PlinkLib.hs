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
{-@ vecVar :: strs:[String] -> {v:DSL p | isVector v && vlength v = len strs} @-}
vecVar :: [String] -> DSL p
vecVar strs = fromList (map' VAR strs)

-- List-like functions ---------------------------------------------------------
{-@ fromList :: l:[{v:DSL p | unpacked v}] ->
               {v:DSL p | isVector v && vlength v = len l} @-}
fromList :: [DSL p] -> DSL p
fromList []     = NIL
fromList (x:xs) = x `CONS` fromList xs

{-@ get :: v:{DSL p | isVector v} -> Btwn 0 (vlength v) -> DSL p @-}
get :: DSL p -> Int -> DSL p
get (CONS p _ ) 0 = p
get (CONS _ ps) i = get ps (i-1)

{-@ set :: v:{DSL p | isVector v} -> Btwn 0 (vlength v) ->
           {x:DSL p | unpacked x} ->
           {u:DSL p | isVector u && vlength u = vlength v} @-}
set :: DSL p -> Int -> DSL p -> DSL p
set (CONS _ ps) 0 x = CONS x ps
set (CONS p ps) i x = CONS p (set ps (i-1) x)

{-@ (+++) :: u:{DSL p | isVector u} ->
             v:{DSL p | isVector v} ->
             {w:DSL p | isVector w && vlength w = vlength u + vlength v} @-}
(+++) :: DSL p -> DSL p -> DSL p
(NIL)       +++ ys = ys
(CONS x xs) +++ ys = CONS x (xs +++ ys)

infixr 5 +++

{-@ vConcat :: vs:[{v:DSL p | isVector v}]
            -> {v:DSL p | isVector v && vlength v = lengths vs} @-}
vConcat :: [DSL p] -> DSL p
vConcat ([])   = NIL
vConcat (p:ps) = p +++ vConcat ps

{-@ reflect lengths @-}
{-@ lengths :: [{v:DSL p | isVector v}] -> Nat @-}
lengths :: [DSL p] -> Int
lengths [] = 0
lengths (p:ps) = vlength p + lengths ps

{-@ vTakeDrop :: n:Nat -> u:{DSL p | isVector u && vlength u >= n} ->
                ({v:DSL p | isVector v && vlength v = n},
                 {w:DSL p | isVector w && vlength w = (vlength u) - n}) @-}
vTakeDrop :: Int -> DSL p -> (DSL p, DSL p)
vTakeDrop 0 xs          = (NIL, xs)
vTakeDrop n (CONS x xs) = let (ys, zs) = vTakeDrop (n-1) xs in (CONS x ys, zs)

{-@ vReplicate :: n:Nat -> {p:DSL p | unpacked p} ->
                  {v:DSL p | isVector v && vlength v = n} @-}
vReplicate :: Int -> DSL p -> DSL p
vReplicate 0 _ = NIL
vReplicate n p = CONS p (vReplicate (n-1) p)

{-@ vZip :: u:{DSL p | isVector u} ->
            v:{DSL p | isVector v && vlength v = vlength u} ->
            w:{[({x:DSL p | unpacked x},
                 {y:DSL p | unpacked y})] |
                 len w = vlength u} @-}
vZip :: DSL p -> DSL p -> [(DSL p, DSL p)]
vZip (NIL)       (NIL)       = []
vZip (CONS x xs) (CONS y ys) = (x,y) : vZip xs ys

{-@ vZipWith :: op:({x:DSL p | unpacked x} ->
                    {y:DSL p | unpacked y} ->
                    {z:DSL p | unpacked z}) ->
                u:{DSL p | isVector u} ->
                v:{DSL p | isVector v && vlength v = vlength u} ->
                w:{DSL p | isVector w && vlength w = vlength u} @-}
vZipWith :: (DSL p -> DSL p -> DSL p) -> DSL p -> DSL p -> DSL p
vZipWith _  (NIL)       (NIL)       = NIL
vZipWith op (CONS x xs) (CONS y ys) = op x y `CONS` vZipWith op xs ys

{-@ vMap :: op:({x:DSL p | unpacked x} -> {y:DSL p | unpacked y})
         -> u:{DSL p | isVector u}
         -> v:{DSL p | isVector v && vlength v = vlength u} @-}
vMap :: (DSL p -> DSL p) -> DSL p -> DSL p
vMap _  (NIL)       = NIL
vMap op (CONS x xs) = op x `CONS` vMap op xs

{-@ vChunk :: n:Nat1 -> v:{DSL p | isVector v && (vlength v) mod n = 0}
           -> {l:[{w:DSL p | isVector w && vlength w = n}]
                | n * len l = vlength v}
            / [vlength v] @-}
vChunk :: Int -> DSL p -> [DSL p]
vChunk _ NIL = []
vChunk n xs  = let (ys, zs) = vTakeDrop n xs in ys : (vChunk n zs)

-- Bitwise operations ----------------------------------------------------------
{-@ vNot :: u:{DSL p | isVector u} ->
            w:{DSL p | isVector w && vlength w = vlength u} @-}
vNot = vMap NOT

{-@ vAnd :: u:{DSL p | isVector u} ->
            v:{DSL p | isVector v && vlength v = vlength u} ->
            w:{DSL p | isVector w && vlength w = vlength u} @-}
vAnd = vZipWith AND

{-@ vOr :: u:{DSL p | isVector u} ->
           v:{DSL p | isVector v && vlength v = vlength u} ->
           w:{DSL p | isVector w && vlength w = vlength u} @-}
vOr = vZipWith OR

{-@ vXor :: u:{DSL p | isVector u} ->
            v:{DSL p | isVector v && vlength v = vlength u} ->
            w:{DSL p | isVector w && vlength w = vlength u} @-}
vXor = vZipWith XOR

-- Shift & rotate --------------------------------------------------------------
{-@ rotateL :: u:{DSL p | isVector u} -> Btwn 0 (vlength u) ->
               {v:DSL p | isVector v && vlength v = vlength u} @-}
rotateL :: DSL p -> Int -> DSL p
rotateL xs n = let (ys, zs) = vTakeDrop n xs in zs +++ ys

{-@ rotateR :: u:{DSL p | isVector u} -> Btwn 0 (vlength u) ->
               {v:DSL p | isVector v && vlength v = vlength u} @-}
rotateR :: DSL p -> Int -> DSL p
rotateR xs n = let (ys, zs) = vTakeDrop (vlength xs - n) xs in zs +++ ys

{-@ shiftL :: u:{DSL p | isVector u} -> Btwn 0 (vlength u) ->
              {v:DSL p | isVector v && vlength v = vlength u} @-}
shiftL :: Num p => DSL p -> Int -> DSL p
shiftL xs n = let (_, zs) = vTakeDrop n xs in
  zs +++ vReplicate n (CONST 0)

{-@ shiftR :: u:{DSL p | isVector u} -> Btwn 0 (vlength u) ->
              {v:DSL p | isVector v && vlength v = vlength u} @-}
shiftR :: Num p => DSL p -> Int -> DSL p
shiftR xs n = let (ys, _) = vTakeDrop (vlength xs - n) xs in
  vReplicate n (CONST 0) +++ ys

-- Integers mod 2^n -----------------------------------------------------------
{-@ fromInt :: n:Nat -> x:Btwn 0 (pow 2 n) ->
              {v:DSL p | isVector v && vlength v = n} @-}
fromInt :: Num p => Int -> Int -> DSL p
fromInt n = go 0 NIL where
  {-@ go :: m:{Nat | m <= n} ->
            {acc:DSL p | isVector acc && vlength acc = m} ->
            x:Btwn 0 (pow 2 n) ->
            {v:DSL p | isVector v && vlength v = n} / [n-m] @-}
  go :: Num p => Int -> DSL p -> Int -> DSL p
  go m acc x
    | m == n    = acc
    | otherwise = let (q, r) = divMod x 2; r' = fromIntegral r
                  in go (m+1) (CONST r' `CONS` acc) q


-- FIXME: this should use DSL types to ensure the argument is a vector of {0,1}
{-@ binaryValue :: {v:DSL p | isVector v && vlength v > 0}
               -> GlobalStore p ({y:DSL p | unpacked y}) @-}
binaryValue :: (Integral p, Fractional p, Eq p) =>
               DSL p -> GlobalStore p (DSL p)
binaryValue v = go v (CONST 0) where
  {-@ go :: {v:DSL p | isVector v} -> {acc:DSL p | unpacked acc}
         -> GlobalStore p ({res:DSL p | unpacked res}) @-}
  go :: (Integral p, Fractional p, Eq p) =>
        DSL p -> DSL p -> GlobalStore p (DSL p)
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

{-@ fromBinary :: {v:DSL p | isVector v && vlength v > 0}
               -> GlobalStore p ({x:DSL p | unpacked x}) @-}
fromBinary :: (Integral p, Fractional p, Eq p) =>
              DSL p -> GlobalStore p (DSL p)
fromBinary vec = do
  let x' = var "x"
  let x = VAR x'

  val <- binaryValue vec
  assert $ val `EQA` x
  define x' (eval val) -- evaluate `val` (value) to a field element
  return x

{-@ toBinary :: n:Nat1 -> {x:DSL p | unpacked x}
             -> GlobalStore p ({v:DSL p | isVector v && vlength v = n}) @-}
toBinary :: (Integral p, Fractional p, Eq p) =>
            Int -> DSL p -> GlobalStore p (DSL p)
toBinary n x = do
  let vec' = vars n "bits"
  let vec = vecVar vec'

  val <- binaryValue vec
  assert $ val `EQA` x
  defineVec vec' (\v -> binaryRepr n <$> eval x v)
  return vec


{-@ addMod :: {m:DSL p | unpacked m}
           -> {x:DSL p | unpacked x} -> {y:DSL p | unpacked y}
           -> GlobalStore p ({z:DSL p | unpacked z}) @-}
addMod :: (Integral p, Fractional p, Ord p) =>
          DSL p -> DSL p -> DSL p -> GlobalStore p (DSL p)
addMod modulus x y = do
  let b = var "overflow"
  let z = var "sum"
  assert $ BOOL (VAR b)
  assert $ (x `ADD` y) `EQA` (VAR z `ADD` (VAR b `MUL` modulus))
  -- TODO: missing assertion that z is < modulus. lookup tables?
  define b (\v -> (\x y m -> if x + y < m then 0 else 1)
                   <$> eval x v <*> eval y v
                   <*> (eval modulus v >>=
                        \x -> if x /= 0 then Just x else Nothing))
  define z (\v -> (\x y m -> (x + y) `mod` m)
                   <$> eval x v <*> eval y v
                   <*> (eval modulus v >>=
                        \x -> if x /= 0 then Just x else Nothing))
  return (VAR z)
