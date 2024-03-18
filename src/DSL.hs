{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
module DSL where

import qualified Data.Set as S

import Constraints
import RefinementTypes()
import ArithmeticGates
import Circuits

import Utils (allRange) -- needed to use ‘satisfies’ in the reflection
import Vec

import GHC.TypeNats (KnownNat)
import PrimitiveRoot

-- The type variable ‘i’ should be understood as the set of wire indices
data KnownNat p => DSL p i =
  WIRE  i                   | -- wire (i.e. variable)
  CONST (F p)               | -- constant
  ADD   (DSL p i) (DSL p i) | -- field addition
  MUL   (DSL p i) (DSL p i)   -- field multiplication


{-@ reflect wires @-}
wires :: (KnownNat p, Ord i) => DSL p i -> S.Set i
wires (WIRE n)    = S.singleton n
wires (CONST _)   = S.empty
wires (ADD p1 p2) = wires p1 `S.union` wires p2
wires (MUL p1 p2) = wires p1 `S.union` wires p2


{-@ assume enumFromTo :: x:a -> y:a -> [{v:a | x <= v && v <= y}] @-}
-- find a wire index that has not been used yet

-- TODO: ideally, this should only be called with sets strictly contained in
-- {0..m-1}; otherwise, there will be no fresh index to return. Is it possible
-- to specify that the second argument should have size < m?
{-@ freshIndex :: m:Nat1 -> S.Set (Btwn Int 0 m) -> Btwn Int 0 m @-}
freshIndex :: Int -> S.Set Int -> Int
freshIndex m used = freshIndex_ [0..m-1] where
  {-@ freshIndex_ :: [Btwn Int 0 m] -> Btwn Int 0 m @-}
  freshIndex_ []     = 0 -- FIXME: this should never be reached
  freshIndex_ (x:xs) = if x `S.notMember` used then x else freshIndex_ xs


-- the number of gates needed to compile the program into a circuit
{-@ measure nGates @-}
{-@ nGates :: DSL p i -> Nat @-}
nGates :: KnownNat p => DSL p i -> Int
nGates (WIRE _)    = 0
nGates (CONST _)   = 1
nGates (ADD p1 p2) = 1 + nGates p1 + nGates p2
nGates (MUL p1 p2) = 1 + nGates p1 + nGates p2


-- compile the program into a circuit including the output wire index
{-@ compile :: m:{v:Int | v >= 3} ->
               c:DSL p (Btwn Int 0 m) ->
               (Circuit (F p) (nGates c) m, Btwn Int 0 m) @-}
compile :: (KnownNat p, PrimitiveRoot (F p)) =>
           Int -> DSL p Int -> (Circuit (F p), Int)
compile m program = xy $ compile' program (wires program) where
  xy (x,y,_) = (x,y)
  {-@ compile' :: c:DSL p (Btwn Int 0 m) -> S.Set (Btwn Int 0 m) ->
                  (Circuit (F p) (nGates c) m, Btwn Int 0 m, S.Set (Btwn Int 0 m)) @-}
  compile' :: (KnownNat p, PrimitiveRoot (F p)) =>
              DSL p Int -> S.Set Int -> (Circuit (F p), Int, S.Set Int)
  compile' (WIRE i) usedWires = (emptyCircuit m, i, S.singleton i)
  compile' (CONST x) usedWires = (constGate m x i, i, S.singleton i)
    where i = freshIndex m usedWires
  compile' (ADD p1 p2) usedWires = (c, i, is)
    where
      i = freshIndex m usedWires
      (c1, i1, is1) = compile' p1 (usedWires `S.union` S.singleton i)
      (c2, i2, is2) = compile' p2 (usedWires `S.union` S.singleton i `S.union` is1)
      n1 = nGates p1; n2 = nGates p2
      c' = join n1 n2 (n1+n2) m c1 c2
      c = join 1 (n1+n2) (1+n1+n2) m (addGate m [i1, i2, i]) c'
      is = S.singleton i `S.union` is1 `S.union` is2
  compile' (MUL p1 p2) usedWires = (c, i, is)
    where
      i = freshIndex m usedWires
      (c1, i1, is1) = compile' p1 (usedWires `S.union` S.singleton i)
      (c2, i2, is2) = compile' p2 (usedWires `S.union` S.singleton i `S.union` is1)
      n1 = nGates p1; n2 = nGates p2
      c' = join n1 n2 (n1+n2) m c1 c2
      c = join 1 (n1+n2) (1+n1+n2) m (mulGate m [i1, i2, i]) c'
      is = S.singleton i `S.union` is1 `S.union` is2


-- the semantics of a program is a function that, given a mapping from wire
-- indices to field values (one for each wire), returns the result of running
-- the program on said field values
{-@ reflect semantics @-}
{-@ semantics :: DSL p i -> (i -> F p) -> F p @-}
semantics :: KnownNat p => DSL p i -> (i -> F p) -> F p
semantics (WIRE i)    input = input i
semantics (CONST x)   input = x
semantics (ADD p1 p2) input = semantics p1 input + semantics p2 input
semantics (MUL p1 p2) input = semantics p1 input * semantics p2 input


{-@ verifyCompile :: m:{v:Int | v >= 3} ->
                     DSL p (Btwn Int 0 m) -> VecN (F p) m -> Bool @-}
verifyCompile :: (KnownNat p, PrimitiveRoot (F p)) =>
                 Int -> DSL p Int -> Vec (F p) -> Bool
verifyCompile m program input = semantics_ == satisfies_
  where
    (circuit, outputWire) = compile m program
    semantics_ = semantics program (input !) == input ! outputWire
    satisfies_ = satisfies (nGates program) m input circuit
