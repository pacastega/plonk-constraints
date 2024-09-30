{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}

module PlinkLib where

import DSL

-- Bit-wise applications -------------------------------------------------------
{-@ bitwise :: op:({x:DSL p i | unpacked x} ->
                   {y:DSL p i | unpacked y} ->
                   {z:DSL p i | unpacked z}) ->
               u:{DSL p i | isVector u} ->
               v:{DSL p i | isVector v && vlength v = vlength u} ->
               w:{DSL p i | isVector w && vlength w = vlength u} @-}
bitwise :: (DSL p i -> DSL p i -> DSL p i) -> DSL p i -> DSL p i -> DSL p i
bitwise _  (NIL)       (NIL)       = NIL
bitwise op (CONS x xs) (CONS y ys) = op x y `CONS` bitwise op xs ys

-- List-like functions ---------------------------------------------------------
{-@ vAppend :: u:{DSL p i | isVector u} ->
               v:{DSL p i | isVector v} ->
               {w:DSL p i | isVector w && vlength w = vlength u + vlength v} @-}
vAppend :: DSL p i -> DSL p i -> DSL p i
vAppend (NIL)       ys = ys
vAppend (CONS x xs) ys = CONS x (vAppend xs ys)

{-@ vTakeDrop :: n:Nat -> u:{DSL p i | isVector u && vlength u >= n} ->
                ({v:DSL p i | isVector v && vlength v = n},
                 {w:DSL p i | isVector w && vlength w = (vlength u) - n}) @-}
vTakeDrop :: Int -> DSL p i -> (DSL p i, DSL p i)
vTakeDrop 0 xs          = (NIL, xs)
vTakeDrop n (CONS x xs) = let (ys, zs) = vTakeDrop (n-1) xs in (CONS x ys, zs)

{-@ vReplicate :: n:Nat -> {p:DSL p i | unpacked p} ->
                  {v:DSL p i | isVector v && vlength v = n} @-}
vReplicate :: Int -> DSL p i -> DSL p i
vReplicate 0 _ = NIL
vReplicate n p = CONS p (vReplicate (n-1) p)

-- Shift & rotate --------------------------------------------------------------
{-@ rotateL :: u:{DSL p i | isVector u} -> Btwn 0 (vlength u) ->
               {v:DSL p i | isVector v && vlength v = vlength u} @-}
rotateL :: DSL p i -> Int -> DSL p i
rotateL xs n = let (ys, zs) = vTakeDrop n xs in zs `vAppend` ys

{-@ rotateR :: u:{DSL p i | isVector u} -> Btwn 0 (vlength u) ->
               {v:DSL p i | isVector v && vlength v = vlength u} @-}
rotateR :: DSL p i -> Int -> DSL p i
rotateR xs n = let (ys, zs) = vTakeDrop (vlength xs - n) xs in zs `vAppend` ys

{-@ shiftL :: u:{DSL p i | isVector u} -> Btwn 0 (vlength u) ->
              {v:DSL p i | isVector v && vlength v = vlength u} @-}
shiftL :: Num p => DSL p i -> Int -> DSL p i
shiftL xs n = let (_, zs) = vTakeDrop n xs in
  zs `vAppend` vReplicate n (CONST 0)

{-@ shiftR :: u:{DSL p i | isVector u} -> Btwn 0 (vlength u) ->
              {v:DSL p i | isVector v && vlength v = vlength u} @-}
shiftR :: Num p => DSL p i -> Int -> DSL p i
shiftR xs n = let (ys, _) = vTakeDrop (vlength xs - n) xs in
  vReplicate n (CONST 0) `vAppend` ys
