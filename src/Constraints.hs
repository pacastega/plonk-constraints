{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# OPTIONS -Wno-unused-imports #-}
{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Constraints (checkGate, satisfies, Circuit) where

import Vec
import RefinementTypes()


-- n == # gates
-- m == # wires

{-@ type Gate p M = (ListN (Btwn 0 M) 3, ListN p 5) @-}
type Gate p = ([Int], [p])

{-@ type Circuit p N M = ListN (Gate p M) N @-}
type Circuit p = [Gate p]



{-@ reflect checkGate @-}
{-@ checkGate :: m:Nat -> VecN p m -> Gate p m -> Bool @-}
checkGate :: (Eq p, Num p) => Int -> Vec p -> Gate p -> Bool
checkGate _ x ([a,b,c], [qL,qR,qO,qM,qC]) =
  qL*x!a + qR*x!b + qO*x!c + qM*x!a*x!b + qC == 0


{-@ reflect satisfies @-}
{-@ satisfies :: n:Nat -> m:Nat -> VecN p m -> Circuit p n m -> Bool @-}
-- Check that the input (values in wires) satisfies the circuit:
satisfies :: (Eq p, Num p) => Int -> Int -> Vec p -> Circuit p -> Bool
satisfies _ _ _     []     = True
satisfies n m input (g:gs) = checkGate m input g && satisfies (n-1) m input gs


{-@ transpose :: n:Nat -> m:Nat ->
                 Circuit p n m ->
                 (ListN (ListN (Btwn 0 m) n) 3, ListN (ListN p n) 5) @-}
transpose :: Int -> Int -> Circuit p -> ([[Int]], [[p]])
transpose _ _ [] = let
    a = []; b = []; c = [];
    qL = []; qR = []; qO = []; qM = []; qC = []
  in ([a, b, c],  [qL, qR, qO, qM, qC])
transpose n m (([a, b, c], [qL, qR, qO, qM, qC]) : gs) = let
    ([as, bs, cs],  [qLs, qRs, qOs, qMs, qCs]) = transpose (n-1) m gs
  in ([a:as, b:bs, c:cs],  [qL:qLs, qR:qRs, qO:qOs, qM:qMs, qC:qCs])
