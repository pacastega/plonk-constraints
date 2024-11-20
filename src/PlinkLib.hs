{-# OPTIONS_GHC -Wno-missing-signatures -Wno-name-shadowing
                -fno-cse -fno-full-laziness #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ infix +++ @-}

module PlinkLib where

import DSL
import Utils (pow)

import GlobalStore

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

{-@ measure isHexDigit @-}
isHexDigit :: Char -> Bool
isHexDigit '0' = True
isHexDigit '1' = True
isHexDigit '2' = True
isHexDigit '3' = True
isHexDigit '4' = True
isHexDigit '5' = True
isHexDigit '6' = True
isHexDigit '7' = True
isHexDigit '8' = True
isHexDigit '9' = True

isHexDigit 'a' = True
isHexDigit 'b' = True
isHexDigit 'c' = True
isHexDigit 'd' = True
isHexDigit 'e' = True
isHexDigit 'f' = True

isHexDigit 'A' = True
isHexDigit 'B' = True
isHexDigit 'C' = True
isHexDigit 'D' = True
isHexDigit 'E' = True
isHexDigit 'F' = True

isHexDigit _   = False

{-@ fromHex :: h:[{c:Char | isHexDigit c}] ->
               {v:DSL p | isVector v && vlength v = 4 * len h} @-}
fromHex :: Num p => String -> DSL p
fromHex []     = NIL
fromHex (c:cs) = go c +++ (fromHex cs) where
  {-@ go :: {c:Char | isHexDigit c} ->
            {v:DSL p | isVector v && vlength v = 4} @-}
  go :: Num p => Char -> DSL p
  go '0' = fromList $ map CONST [0,0,0,0]
  go '1' = fromList $ map CONST [0,0,0,1]
  go '2' = fromList $ map CONST [0,0,1,0]
  go '3' = fromList $ map CONST [0,0,1,1]
  go '4' = fromList $ map CONST [0,1,0,0]
  go '5' = fromList $ map CONST [0,1,0,1]
  go '6' = fromList $ map CONST [0,1,1,0]
  go '7' = fromList $ map CONST [0,1,1,1]
  go '8' = fromList $ map CONST [1,0,0,0]
  go '9' = fromList $ map CONST [1,0,0,1]

  go 'a' = fromList $ map CONST [1,0,1,0]
  go 'b' = fromList $ map CONST [1,0,1,1]
  go 'c' = fromList $ map CONST [1,1,0,0]
  go 'd' = fromList $ map CONST [1,1,0,1]
  go 'e' = fromList $ map CONST [1,1,1,0]
  go 'f' = fromList $ map CONST [1,1,1,1]

  go 'A' = fromList $ map CONST [1,0,1,0]
  go 'B' = fromList $ map CONST [1,0,1,1]
  go 'C' = fromList $ map CONST [1,1,0,0]
  go 'D' = fromList $ map CONST [1,1,0,1]
  go 'E' = fromList $ map CONST [1,1,1,0]
  go 'F' = fromList $ map CONST [1,1,1,1]

{-@ vecAdd :: u:{DSL p | isVector u} ->
              v:{DSL p | isVector v && vlength v = vlength u} ->
              GlobalStore (DSL p)
                          ({w:DSL p | isVector w && vlength w = vlength u}) @-}
vecAdd :: Num p => DSL p -> DSL p -> GlobalStore (DSL p) (DSL p)
vecAdd u v = GStore result store
  where
    (result, (_, store)) = aux u v

    {-@ aux :: x:{DSL p | isVector x}
            -> y:{DSL p | isVector y && vlength y = vlength x}
            -> res:{({z:DSL p | isVector z},
                       ({c:DSL p | unpacked c}, Store p))
                    | vlength (fst res) = vlength x} @-}
    aux :: Num p => DSL p -> DSL p -> (DSL p, (DSL p, Store p))
    aux (NIL)       (NIL)       = (NIL, (CONST 0, []))
    aux (CONS u us) (CONS v vs) = addWithCarry (u, v) (aux us vs)


{-@ addWithCarry :: ({x:DSL p | unpacked x}, {y:DSL p | unpacked y})
                 -> acc:({v:DSL p | isVector v},
                           ({v:DSL p | unpacked v}, Store p))
                 -> res:{({v:DSL p | isVector v},
                           ({v:DSL p | unpacked v}, Store p))
                         | vlength (fst res) = 1 + vlength (fst acc)}
@-} --TODO: change "fst" to "fst3" and go back to triples
addWithCarry :: Num p => (DSL p, DSL p)
             -> (DSL p, (DSL p, Store p))
             -> (DSL p, (DSL p, Store p))
addWithCarry (x, y) (acc, (carry, store)) =
  ((sum `EQLC` 1) `UnsafeOR` (sum `EQLC` 3) `CONS` acc, -- new acc
   (VAR nextCarry,                                      -- new carry
    store ++ [DEF nextCarry $ (sum `EQLC` 2) `UnsafeOR` (sum `EQLC` 3)])
  )

  where
    sum = (x `ADD` y) `ADD` carry
    nextCarry = var "nextCarry"

-- FIXME: this should use DSL types to ensure the argument is a vector of {0,1}
{-@ binaryValue :: {v:DSL p | isVector v && vlength v > 0}
               -> GlobalStore (DSL p) ({y:DSL p | unpacked y}) @-}
binaryValue :: Num p => DSL p -> GlobalStore (DSL p) (DSL p)
binaryValue v = go v (CONST 0) where
  {-@ go :: {v:DSL p | isVector v} -> {acc:DSL p | unpacked acc}
         -> GlobalStore (DSL p) ({res:DSL p | unpacked res}) @-}
  go :: Num p => DSL p -> DSL p -> GlobalStore (DSL p) (DSL p)
  go NIL         acc = pure acc
  go (CONS x xs) acc = do
    let bit = var "bit"
    assert $ DEF bit x
    assert $ BOOL (VAR bit)
    go xs (VAR bit `ADD` (acc `MUL` CONST 2))

{-@ fromBinary :: {v:DSL p | isVector v && vlength v > 0}
               -> GlobalStore (DSL p) ({x:DSL p | unpacked x}) @-}
fromBinary :: Num p => DSL p -> GlobalStore (DSL p) (DSL p)
fromBinary vec = do
  let x = VAR (var "x")
  val <- binaryValue vec
  assert $ val `EQA` x
  return x

{-@ toBinary :: n:Nat1 -> {x:DSL p | unpacked x}
             -> GlobalStore (DSL p) ({v:DSL p | isVector v && vlength v = n}) @-}
toBinary :: Num p => Int -> DSL p -> GlobalStore (DSL p) (DSL p)
toBinary n x = do
  let vec = vecVar n "bits"
  val <- binaryValue vec
  assert $ val `EQA` x
  return vec


{-@ addMod :: {m:DSL p | unpacked m}
           -> {x:DSL p | unpacked x} -> {y:DSL p | unpacked y}
           -> GlobalStore (DSL p) ({z:DSL p | unpacked z}) @-}
addMod :: DSL p -> DSL p -> DSL p -> GlobalStore (DSL p) (DSL p)
addMod modulus x y = do
  let b = var "overflow"
  let z = var "sum"
  assert $ BOOL (VAR b)
  assert $ (x `ADD` y) `EQA` (VAR z `ADD` (VAR b `MUL` modulus))
  -- TODO: missing assertion that z is < modulus. lookup tables?
  return (VAR z)
