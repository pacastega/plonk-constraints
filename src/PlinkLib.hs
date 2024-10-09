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


-- FIXME: this is VERY inefficient:
-- 1. the (double) addition ‘x+y+c’ gets computed 4 times
-- 2. the comparisons against constants use 3 constraints, instead of 2
-- 3. the comparison ‘sum == 3’ gets computed twice
{-@ vecAdd :: u:{DSL p | isVector u} ->
              v:{DSL p | isVector v && vlength v = vlength u} ->
                DSL p @-}
  -- TODO: it also preserves length
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
