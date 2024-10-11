{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}

module PlinkLib where

import DSL
import Utils (pow)

-- Bit-wise applications -------------------------------------------------------
{-@ bitwise :: op:({x:DSL p | unpacked x} ->
                   {y:DSL p | unpacked y} ->
                   {z:DSL p | unpacked z}) ->
               u:{DSL p | isVector u} ->
               v:{DSL p | isVector v && vlength v = vlength u} ->
               w:{DSL p | isVector w && vlength w = vlength u} @-}
bitwise :: (DSL p -> DSL p -> DSL p) -> DSL p -> DSL p -> DSL p
bitwise _  (NIL)       (NIL)       = NIL
bitwise op (CONS x xs) (CONS y ys) = op x y `CONS` bitwise op xs ys

-- List-like functions ---------------------------------------------------------
{-@ fromList :: l:[{v:DSL p | unpacked v}] ->
               {v:DSL p | isVector v && vlength v = len l} @-}
fromList :: [DSL p] -> DSL p
fromList []     = NIL
fromList (x:xs) = x `CONS` fromList xs

{-@ vAppend :: u:{DSL p | isVector u} ->
               v:{DSL p | isVector v} ->
               {w:DSL p | isVector w && vlength w = vlength u + vlength v} @-}
vAppend :: DSL p -> DSL p -> DSL p
vAppend (NIL)       ys = ys
vAppend (CONS x xs) ys = CONS x (vAppend xs ys)

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

-- Shift & rotate --------------------------------------------------------------
{-@ rotateL :: u:{DSL p | isVector u} -> Btwn 0 (vlength u) ->
               {v:DSL p | isVector v && vlength v = vlength u} @-}
rotateL :: DSL p -> Int -> DSL p
rotateL xs n = let (ys, zs) = vTakeDrop n xs in zs `vAppend` ys

{-@ rotateR :: u:{DSL p | isVector u} -> Btwn 0 (vlength u) ->
               {v:DSL p | isVector v && vlength v = vlength u} @-}
rotateR :: DSL p -> Int -> DSL p
rotateR xs n = let (ys, zs) = vTakeDrop (vlength xs - n) xs in zs `vAppend` ys

{-@ shiftL :: u:{DSL p | isVector u} -> Btwn 0 (vlength u) ->
              {v:DSL p | isVector v && vlength v = vlength u} @-}
shiftL :: Num p => DSL p -> Int -> DSL p
shiftL xs n = let (_, zs) = vTakeDrop n xs in
  zs `vAppend` vReplicate n (CONST 0)

{-@ shiftR :: u:{DSL p | isVector u} -> Btwn 0 (vlength u) ->
              {v:DSL p | isVector v && vlength v = vlength u} @-}
shiftR :: Num p => DSL p -> Int -> DSL p
shiftR xs n = let (ys, _) = vTakeDrop (vlength xs - n) xs in
  vReplicate n (CONST 0) `vAppend` ys

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
fromHex (c:cs) = go c `vAppend` (fromHex cs) where
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
                DSL p @-}
vecAdd :: Num p => DSL p -> DSL p -> DSL p
vecAdd u v = localBindings env (fromList result)
  where
    (result, _, env, _) = foldr addWithCarry ([], CONST 0, [], 0) (vZip u v)

    {-@ addWithCarry :: ({x:DSL p | unpacked x},
                         {y:DSL p | unpacked y})
                     -> ([{v:DSL p | unpacked v}],
                          {v:DSL p | unpacked v},
                          [(String, {v:DSL p | unpacked v})],
                          Nat)
                     -> ([{v:DSL p | unpacked v}],
                          {v:DSL p | unpacked v},
                          [(String, {v:DSL p | unpacked v})],
                          Nat)
    @-}
    addWithCarry :: Num p => (DSL p, DSL p) ->
                             ([DSL p], DSL p, [(String, DSL p)], Int) ->
                             ([DSL p], DSL p, [(String, DSL p)], Int)
    addWithCarry (x, y) (acc, carry, env, i) =
      (result : acc, -- new acc
       VAR carryStr, -- new carry
       env',         -- new environment
       i+1           -- add the next bit in the vector
      ) where
          sum    = (x `ADD` y) `ADD` carry
          result = (VAR sumStr `EQLC` 1) `UnsafeOR` (VAR sumStr `EQLC` 3)
          carry' = (VAR sumStr `EQLC` 2) `UnsafeOR` (VAR sumStr `EQLC` 3)

          sumStr   = "sum" ++ show i
          carryStr = "carry" ++ show i
          env'     = env ++ [(sumStr, sum), (carryStr, carry')]


{-@ localBindings :: [(String, {v:DSL p | unpacked v})] -> DSL p -> DSL p @-}
localBindings :: [(String, DSL p)] -> DSL p -> DSL p
localBindings env body = case env of
  []               -> body
  (var,def) : env' -> LET var def (localBindings env' body)
