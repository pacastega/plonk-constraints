{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
module DSL where

import qualified Data.Set as S --(empty, singleton, union, notMember)

import Constraints
import RefinementTypes()
import ArithmeticGates
import Circuits

import Vec

import GHC.TypeNats (KnownNat)
import PrimitiveRoot

-- {-@ data DSL p M =
--          WIRE  {i::Btwn Int 0 M}   |
--          CONST (F p)               |
--          ADD   (DSL p M) (DSL p M) |
--          MUL   (DSL p M) (DSL p M)
-- @-}

-- TODO: we should specify that WIRE takes an argument between 0 and m-1 (where
-- m is the maximum number of wires there can be in the circuit). This probably
-- requires including m as a parameter to DSL. Is there a simple way to do this?
-- Do we need GADTs?
--
-- Either way, we need to take into account that the wires used explicitly are
-- not all we need: we also need wires to connect the gates between themselves
-- (intermediate computations).

{-@ data DSL p =
         WIRE  Nat             |
         CONST (F p)           |
         ADD   (DSL p) (DSL p) |
         MUL   (DSL p) (DSL p)
@-}
data KnownNat p => DSL p =
  WIRE  Int             | -- wire (i.e. variable)
  CONST (F p)           | -- constant
  ADD   (DSL p) (DSL p) | -- field addition
  MUL   (DSL p) (DSL p)   -- field multiplication


-- return the set of wire indices that appear in the program
-- FIXME: this specification needs including m in DSL
-- {-@ wires :: DSL p => Set (Btwn Int 0 m) @-}

{-@ wires :: DSL p -> S.Set Nat @-}
wires :: KnownNat p => DSL p -> S.Set Int
wires program = case program of
  WIRE n    -> S.singleton n
  CONST _   -> S.empty
  ADD p1 p2 -> wires p1 `S.union` wires p2
  MUL p1 p2 -> wires p1 `S.union` wires p2


{-@ assume enumFromTo :: x:a -> y:a -> [{v:a | x <= v && v <= y}] @-}
-- find a wire index that has not been used yet
{-@ freshIndex :: m:Nat1 -> S.Set Nat -> Btwn Int 0 m @-}
freshIndex :: Int -> S.Set Int -> Int
freshIndex m used = freshIndex_ [0..m-1] where
  -- freshIndex_ []     = error "run out of values to check"
  {-@ freshIndex_ :: [Btwn Int 0 m] -> Btwn Int 0 m @-}
  freshIndex_ []     = 0 -- FIXME: this is a quick-and-dirty fix to suppress
                         -- errors about non-exhaustive patterns
  freshIndex_ (x:xs) = if x `S.notMember` used then x else freshIndex_ xs


-- the number of gates needed to compile the program into a circuit
{-@ reflect nGates @-}
{-@ nGates :: DSL p -> Nat @-}
nGates :: KnownNat p => DSL p -> Int
nGates (WIRE i)    = 0
nGates (CONST x)   = 1
nGates (ADD p1 p2) = 1 + nGates p1 + nGates p2
nGates (MUL p1 p2) = 1 + nGates p1 + nGates p2


-- -- the number of wires needed to compile the program into a circuit
-- {-@ reflect nWires @-}
-- {-@ nWires :: DSL p -> Nat1 @-}
-- nWires :: KnownNat p => DSL p -> Int
-- nWires (WIRE i) = 1 -- the wire itself
-- nWires (CONST x) = 2 -- the input wire
-- nWires (ADD p1 p2) = 1 + nWires p1 + nWires p2
-- nWires (MUL p1 p2) = 1 + nWires p1 + nWires p2


-- compile the program into a circuit including the output wire index
{-@ compile :: m:Nat1 ->
               c:DSL p -> (Circuit (F p) (nGates c) m, Btwn Int 0 m) @-}
compile :: (KnownNat p, PrimitiveRoot (F p)) =>
           Int -> DSL p -> (Circuit (F p), Int)
compile m program = (\(x,y,_) -> (x,y)) $ compile' program (wires program) where
  {-@ compile' :: c:DSL p -> S.Set Nat ->
                  (Circuit (F p) (nGates c) m, Btwn Int 0 m, S.Set (Btwn Int 0 m)) @-}
  -- compile' :: DSL p -> S.Set Int -> (Circuit (F p), Int)
  compile' program usedWires = case program of
    WIRE i    -> (emptyCircuit, i, S.singleton i)
    CONST x   -> let i = freshIndex m usedWires in (constGate m x i, i, S.singleton i)
    ADD p1 p2 -> (c, i, is) where
        i = freshIndex m usedWires
        (c1, i1, is1) = compile' p1 (usedWires `S.union` S.singleton i)
        (c2, i2, is2) = compile' p2 (usedWires `S.union` S.singleton i `S.union` is1)
        n1 = nGates p1; n2 = nGates p2
        c' = join n1 n2 (n1+n2) m c1 c2
        c = join 1 (n1+n2) (1+n1+n2) m (addGate [i1, i2, i]) c'
        is = S.singleton i `S.union` is1 `S.union` is2
    MUL p1 p2 -> (c, i, is) where
        i = freshIndex m usedWires
        (c1, i1, is1) = compile' p1 (usedWires `S.union` S.singleton i)
        (c2, i2, is2) = compile' p2 (usedWires `S.union` S.singleton i `S.union` is1)
        n1 = nGates p1; n2 = nGates p2
        c' = join n1 n2 (n1+n2) m c1 c2
        c = join 1 (n1+n2) (1+n1+n2) m (mulGate [i1, i2, i]) c'
        is = S.singleton i `S.union` is1 `S.union` is2
-- FIXME: The right circuit shouldn’t reuse /any/ of the wires used in the left
-- one (right now, it only avoids repeating the output wire).
