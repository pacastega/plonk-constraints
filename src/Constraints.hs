{-# LANGUAGE CPP #-}
{-# OPTIONS -Wno-unused-imports #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Constraints where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import TypeAliases


-- n == # gates
-- m == # wires

data Wire i = Wire i | Free

{-@ measure isWire @-}
isWire :: Wire i -> Bool
isWire (Wire _) = True
isWire Free  = False

{-@ type Gate p M = (ListN (Wire (Btwn 0 M)) 3, ListN p 5) @-}
type Gate p = ([Wire Int], [p])

{-@ type Circuit p N M = ListN ({g:Gate p M | wfGate M g}) N @-}
type Circuit p = [Gate p]

{-@ reflect wfGate @-}
{-@ wfGate :: m:Nat -> Gate p m -> Bool @-}
wfGate :: (Eq p, Num p) => Int -> Gate p -> Bool
wfGate _ ([a,b,c], [qL,qR,qO,qM,qC]) = (isWire a || qL == 0 && qM == 0)
                                      && (isWire b || qR == 0 && qM == 0)
                                      && (isWire c || qO == 0)

{-@ reflect closedGate @-}
{-@ closedGate :: m:Nat -> WireValuation p m -> Gate p m -> Bool @-}
closedGate :: Int -> WireValuation p -> Gate p -> Bool
closedGate m σ g = S.isSubsetOf (wiresG m g) (M.keysSet σ)

{-@ reflect wiresG @-}
{-@ wiresG :: m:Nat -> Gate p m -> S.Set Int @-}
wiresG :: Int -> Gate p -> S.Set Int
wiresG _ ([a,b,c], _) = wireW a `S.union` wireW b `S.union` wireW c

{-@ reflect wireW @-}
wireW :: Wire Int -> S.Set Int
wireW Free = S.empty
wireW (Wire i) = S.singleton i

{-@ reflect wiresC @-}
{-@ wiresC :: n:Nat -> m:Nat -> Circuit p n m -> S.Set Int @-}
wiresC :: Int -> Int -> Circuit p -> S.Set Int
wiresC _ _ []     = S.empty
wiresC n m (g:gs) = wiresG m g `S.union` wiresC (n-1) m gs


{-@ reflect closedCirc @-}
{-@ closedCirc :: n:Nat -> m:Nat -> WireValuation p m -> Circuit p n m -> Bool @-}
closedCirc :: Int -> Int -> WireValuation p -> Circuit p -> Bool
closedCirc n m σ c = S.isSubsetOf (wiresC n m c) (M.keysSet σ)

{-@ reflect checkGate @-}
{-@ checkGate :: m:Nat -> σ:WireValuation p m
              -> {g:Gate p m | wfGate m g && closedGate m σ g} -> Bool @-}
checkGate :: (Eq p, Num p) => Int -> WireValuation p -> Gate p -> Bool
checkGate m σ ([a,b,c], [qL,qR,qO,qM,qC]) =
  qL*xa + qR*xb + qO*xc + qM*xa*xb + qC == 0
    where xa = wireValue m σ a; xb = wireValue m σ b; xc = wireValue m σ c

{-@ reflect wireValue @-}
{-@ wireValue :: m:Nat -> σ:WireValuation p m
              -> ({w:Wire Int | S.isSubsetOf (wireW w) (M.keysSet σ)}) -> p @-}
wireValue :: (Eq p, Num p) => Int -> WireValuation p -> Wire Int -> p
-- since any 'free' wire doesn't contribute, we arbitrarily map it to 0
wireValue _ σ Free = 0
wireValue _ σ (Wire i) = M.lookup' i σ


{-@ reflect satisfies @-}
{-@ satisfies :: n:Nat -> m:Nat -> σ:WireValuation p m
              -> {c:Circuit p n m | closedCirc n m σ c} -> Bool @-}
-- Check that the input (values in wires) satisfies the circuit:
satisfies :: (Eq p, Num p) => Int -> Int -> WireValuation p -> Circuit p -> Bool
satisfies _ _ _ []     = True
satisfies n m σ (g:gs) = checkGate m σ g && satisfies (n-1) m σ gs


{-@ transpose :: n:Nat -> m:Nat ->
                 Circuit p n m ->
                 (ListN (ListN (Wire (Btwn 0 m)) n) 3, ListN (ListN p n) 5) @-}
transpose :: Int -> Int -> Circuit p -> ([[Wire Int]], [[p]])
transpose _ _ [] = let
    a = []; b = []; c = [];
    qL = []; qR = []; qO = []; qM = []; qC = []
  in ([a, b, c],  [qL, qR, qO, qM, qC])
transpose n m (([a, b, c], [qL, qR, qO, qM, qC]) : gs) = let
    ([as, bs, cs],  [qLs, qRs, qOs, qMs, qCs]) = transpose (n-1) m gs
  in ([a:as, b:bs, c:cs],  [qL:qLs, qR:qRs, qO:qOs, qM:qMs, qC:qCs])
