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


-- Labeled DSL
data KnownNat p => LDSL p i =
  LWIRE  i                       |
  LCONST (F p)                 i |
  LADD   (LDSL p i) (LDSL p i) i |
  LMUL   (LDSL p i) (LDSL p i) i
  deriving Show


-- label each constructor with the index of the wire where its output will be
{-@ label :: m:Nat1 -> DSL p (Btwn Int 0 m) -> LDSL p (Btwn Int 0 m) @-}
label :: KnownNat p => Int -> DSL p Int -> LDSL p Int
label m program = fst $ label' program (wires program) where
  {-@ label' :: DSL p (Btwn Int 0 m) -> S.Set (Btwn Int 0 m) ->
                (LDSL p (Btwn Int 0 m), S.Set (Btwn Int 0 m)) @-}
  label' :: (KnownNat p) => DSL p Int -> S.Set Int -> (LDSL p Int, S.Set Int)
  label' (WIRE i) usedWires = (LWIRE i, S.singleton i)
  label' (CONST x) usedWires = (LCONST x i, S.singleton i) where
    i = freshIndex m usedWires
  label' (ADD p1 p2) usedWires = (LADD p1' p2' i, is) where
    i = freshIndex m usedWires
    (p1', is1) = label' p1 (usedWires `S.union` S.singleton i)
    (p2', is2) = label' p2 (usedWires `S.union` S.singleton i `S.union` is1)
    is = S.singleton i `S.union` is1 `S.union` is2
  label' (MUL p1 p2) usedWires = (LMUL p1' p2' i, is) where
    i = freshIndex m usedWires
    (p1', is1) = label' p1 (usedWires `S.union` S.singleton i)
    (p2', is2) = label' p2 (usedWires `S.union` S.singleton i `S.union` is1)
    is = S.singleton i `S.union` is1 `S.union` is2


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
{-@ nGates :: LDSL p i -> Nat @-}
nGates :: KnownNat p => LDSL p i -> Int
nGates (LWIRE _)      = 0
nGates (LCONST _ _)   = 1
nGates (LADD p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LMUL p1 p2 _) = 1 + nGates p1 + nGates p2


-- compile the program into a circuit including the output wire index
{-@ compile :: m:{v:Int | v >= 3} ->
               c:LDSL p (Btwn Int 0 m) ->
               Circuit (F p) (nGates c) m @-}
compile :: (KnownNat p, PrimitiveRoot (F p)) =>
           Int -> LDSL p Int -> Circuit (F p)
compile m program = fst $ compile' program where
  {-@ compile' :: c:LDSL p (Btwn Int 0 m) ->
                  (Circuit (F p) (nGates c) m, Btwn Int 0 m) @-}
  compile' :: (KnownNat p, PrimitiveRoot (F p)) =>
              LDSL p Int -> (Circuit (F p), Int)
  compile' (LWIRE i)      = (emptyCircuit m, i)
  compile' (LCONST x i)   = (constGate m x i, i)
  compile' (LADD p1 p2 i) = (c, i)
    where
      (c1, i1) = compile' p1
      (c2, i2) = compile' p2
      n1 = nGates p1; n2 = nGates p2
      c' = join n1 n2 (n1+n2) m c1 c2
      c = join 1 (n1+n2) (1+n1+n2) m (addGate m [i1, i2, i]) c'
  compile' (LMUL p1 p2 i) = (c, i)
    where
      (c1, i1) = compile' p1
      (c2, i2) = compile' p2
      n1 = nGates p1; n2 = nGates p2
      c' = join n1 n2 (n1+n2) m c1 c2
      c = join 1 (n1+n2) (1+n1+n2) m (mulGate m [i1, i2, i]) c'


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


{-@ semanticsAreCorrect :: m:Nat1 ->
                           LDSL p (Btwn Int 0 m) -> VecN (F p) m ->
                           Bool @-}
semanticsAreCorrect :: KnownNat p => Int -> LDSL p Int -> Vec (F p) -> Bool
semanticsAreCorrect m program input = fst $ aux program where
  {-@ aux :: LDSL p (Btwn Int 0 m) -> (Bool, Btwn Int 0 m) @-}
  aux (LWIRE i)      = (True, i)
  aux (LCONST x i)   = (input!i == x, i)
  aux (LADD p1 p2 i) = (correct, i) where
    (correct1, i1) = aux p1
    (correct2, i2) = aux p2
    correct = correct1 && correct2 && input!i == input!i1 + input!i2
  aux (LMUL p1 p2 i) = (correct, i) where
    (correct1, i1) = aux p1
    (correct2, i2) = aux p2
    correct = correct1 && correct2 && input!i == input!i1 * input!i2


{-@ verifyCompile :: m:{v:Int | v >= 3} ->
                     DSL p (Btwn Int 0 m) -> VecN (F p) m -> Bool @-}
verifyCompile :: (KnownNat p, PrimitiveRoot (F p)) =>
                 Int -> DSL p Int -> Vec (F p) -> Bool
verifyCompile m program input = semantics_ == satisfies_
  where
    labeledProgram = label m program
    semantics_ = semanticsAreCorrect m labeledProgram input

    circuit = compile m labeledProgram
    satisfies_ = satisfies (nGates labeledProgram) m input circuit
