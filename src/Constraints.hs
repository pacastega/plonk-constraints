{-# LANGUAGE CPP #-}
{-# OPTIONS -Wno-unused-imports #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Constraints where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import TypeAliases


-- n == # gates
-- m == # wires

data Wire i = W i | Free

{-@ measure isWire @-}
isWire :: Wire i -> Bool
isWire (W _) = True
isWire Free  = False

{-@ type Gate p M = (ListN (Wire (Btwn 0 M)) 3, ListN p 5) @-}
type Gate p = ([Wire Int], [p])

{-@ type Circuit p N M = ListN ({g:Gate p M | realGate M g}) N @-}
type Circuit p = [Gate p]


{-@ reflect realGate @-}
{-@ realGate :: m:Nat -> Gate p m -> Bool @-}
realGate :: (Eq p, Num p) => Int -> Gate p -> Bool
realGate _ ([a,b,c], [qL,qR,qO,qM,qC]) = (isWire a || qL == 0 && qM == 0)
                                      && (isWire b || qR == 0 && qM == 0)
                                      && (isWire c || qO == 0)


type WireValuation p = M.Map Int p
{-@ type WireValuation p M = M.Map (Btwn 0 M) p @-}


{-@ reflect closedGate @-}
{-@ closedGate :: m:Nat -> WireValuation p m -> Gate p m -> Bool @-}
closedGate :: Int -> WireValuation p -> Gate p -> Bool
closedGate m σ ([a,b,c], _) = boundWire σ a && boundWire σ b && boundWire σ c

{-@ reflect boundWire @-}
boundWire :: WireValuation p -> Wire Int -> Bool
boundWire σ Free  = True
boundWire σ (W i) = M.member i σ

{-@ reflect closedCirc @-}
{-@ closedCirc :: n:Nat -> m:Nat -> WireValuation p m -> Circuit p n m -> Bool @-}
closedCirc :: Int -> Int -> WireValuation p -> Circuit p -> Bool
closedCirc _ _ _ []     = True
closedCirc n m σ (g:gs) = closedGate m σ g && closedCirc (n-1) m σ gs


{-@ reflect checkGate @-}
{-@ checkGate :: m:Nat -> σ:WireValuation p m
              -> {g:Gate p m | realGate m g && closedGate m σ g} -> Bool @-}
checkGate :: (Eq p, Num p) => Int -> WireValuation p -> Gate p -> Bool
checkGate m σ ([a,b,c], [qL,qR,qO,qM,qC]) =
  qL*xa + qR*xb + qO*xc + qM*xa*xb + qC == 0
    where xa = wireValue m σ a; xb = wireValue m σ b; xc = wireValue m σ c

{-@ reflect wireValue @-}
{-@ wireValue :: m:Nat -> σ:WireValuation p m -> {w:Wire Int | boundWire σ w} -> p @-}
wireValue :: (Eq p, Num p) => Int -> WireValuation p -> Wire Int -> p
-- since any 'free' wire doesn't contribute, we arbitrarily map it to 0
wireValue _ σ Free = 0
wireValue _ σ (W i) = M.lookup' i σ


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
