{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--reflection" @-}
module DSL where

import Constraints
import RefinementTypes()
import ArithmeticGates
import Circuits

import Utils
import Vec

import qualified Data.Set as S

-- The type variable ‘i’ should be understood as the set of wire indices
data DSL p i =
  WIRE  i                   | -- wire (i.e. variable)
  CONST p                   | -- constant
  ADD   (DSL p i) (DSL p i) | -- field addition
  MUL   (DSL p i) (DSL p i) | -- field multiplication
  DIV   (DSL p i) (DSL p i) | -- field division

  ISZERO (DSL p i)            -- zero check


-- Labeled DSL
data LDSL p i =
  LWIRE  i                       |
  LCONST p                     i |
  LADD   (LDSL p i) (LDSL p i) i |
  LMUL   (LDSL p i) (LDSL p i) i |
  LDIV   (LDSL p i) (LDSL p i) i |

  LISZERO (LDSL p i)         i i
  deriving Show


-- label each constructor with the index of the wire where its output will be
{-@ label :: m:Nat1 -> DSL p (Btwn 0 m) -> LDSL p (Btwn 0 m) @-}
label :: Int -> DSL p Int -> LDSL p Int
label m program = fst $ label' program (wires program) where
  {-@ label' :: DSL p (Btwn 0 m) -> Vec (Btwn 0 m) ->
                (LDSL p (Btwn 0 m), Vec (Btwn 0 m)) @-}
  label' :: DSL p Int -> Vec Int -> (LDSL p Int, Vec Int)
  label' (WIRE i)  _         = (LWIRE i, singleton i)
  label' (CONST x) usedWires = (LCONST x i, singleton i) where
    i = freshIndex m usedWires
  label' (ADD p1 p2) usedWires = (LADD p1' p2' i, is) where
    i = freshIndex m usedWires
    (p1', is1) = label' p1 (usedWires `append` singleton i)
    (p2', is2) = label' p2 (usedWires `append` singleton i `append` is1)
    is = singleton i `append` is1 `append` is2
  label' (MUL p1 p2) usedWires = (LMUL p1' p2' i, is) where
    i = freshIndex m usedWires
    (p1', is1) = label' p1 (usedWires `append` singleton i)
    (p2', is2) = label' p2 (usedWires `append` singleton i `append` is1)
    is = singleton i `append` is1 `append` is2
  label' (DIV p1 p2) usedWires = (LDIV p1' p2' i, is) where
    i = freshIndex m usedWires
    (p1', is1) = label' p1 (usedWires `append` singleton i)
    (p2', is2) = label' p2 (usedWires `append` singleton i `append` is1)
    is = singleton i `append` is1 `append` is2

  label' (ISZERO p1) usedWires = (LISZERO p1' w i, is) where
    i = freshIndex m usedWires
    w = freshIndex m (usedWires `append` singleton i)
    (p1', is1) = label' p1 (usedWires `append` fromList [i, w])
    is = singleton i `append` singleton w `append` is1


{-@ reflect outputWire @-}
outputWire :: LDSL p i -> i
outputWire (LWIRE i)    = i
outputWire (LCONST _ i) = i
outputWire (LADD _ _ i) = i
outputWire (LMUL _ _ i) = i
outputWire (LDIV _ _ i) = i
outputWire (LISZERO _ _ i) = i


wires :: DSL p i -> Vec i
wires (WIRE n)    = singleton n
wires (CONST _)   = Nil
wires (ADD p1 p2) = wires p1 `append` wires p2
wires (MUL p1 p2) = wires p1 `append` wires p2
wires (DIV p1 p2) = wires p1 `append` wires p2
wires (ISZERO p1) = wires p1


{-@ reflect lwires @-}
lwires :: Ord i => LDSL p i -> S.Set i
lwires (LWIRE n)      = S.singleton n
lwires (LCONST _ _)   = S.empty
lwires (LADD p1 p2 _) = lwires p1 `S.union` lwires p2
lwires (LMUL p1 p2 _) = lwires p1 `S.union` lwires p2
lwires (LDIV p1 p2 _) = lwires p1 `S.union` lwires p2
lwires (LISZERO p1 _ _) = lwires p1


{-@ assume enumFromTo :: x:a -> y:a -> [{v:a | x <= v && v <= y}] @-}
-- find a wire index that has not been used yet

-- TODO: ideally, this should only be called with sets strictly contained in
-- {0..m-1}; otherwise, there will be no fresh index to return. Is it possible
-- to specify that the second argument should have size < m?
{-@ freshIndex :: m:Nat1 -> Vec (Btwn 0 m) -> Btwn 0 m @-}
freshIndex :: Int -> Vec Int -> Int
freshIndex m used = freshIndex_ [0..m-1] where
  {-@ freshIndex_ :: [Btwn 0 m] -> Btwn 0 m @-}
  freshIndex_ []     = 0 -- FIXME: this should never be reached
  freshIndex_ (x:xs) = if x `velem` used then freshIndex_ xs else x


-- the number of gates needed to compile the program into a circuit
{-@ measure nGates @-}
{-@ nGates :: LDSL p i -> Nat @-}
nGates :: LDSL p i -> Int
nGates (LWIRE _)      = 0
nGates (LCONST _ _)   = 1
nGates (LADD p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LMUL p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LDIV p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LISZERO p1 _ _) = 2 + nGates p1


-- compile the program into a circuit including the output wire index
{-@ reflect compile @-}
{-@ compile :: m:{v:Int | v >= 3} ->
               c:LDSL p (Btwn 0 m) ->
               Circuit p (nGates c) m @-}
compile :: Fractional p => Int -> LDSL p Int -> Circuit p
compile m (LWIRE _)      = emptyCircuit m
compile m (LCONST x i)   = constGate m x i
compile m (LADD p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (addGate m [i1, i2, i]) c'
compile m (LMUL p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (mulGate m [i1, i2, i]) c'
compile m (LDIV p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (mulGate m [i, i2, i1]) c'
compile m (LISZERO p1 w i) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (isZeroGate m [i1, w, i]) c1


{-@ reflect semanticsAreCorrect @-}
{-@ semanticsAreCorrect :: m:Nat1 ->
                           LDSL p (Btwn 0 m) -> VecN p m ->
                           Bool @-}
semanticsAreCorrect :: (Eq p, Fractional p) => Int -> LDSL p Int -> Vec p -> Bool
semanticsAreCorrect _ (LWIRE _)      _     = True
semanticsAreCorrect _ (LCONST x i)   input = input!i == x
semanticsAreCorrect m (LADD p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 && input!i == input!i1 + input!i2
semanticsAreCorrect m (LMUL p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 && input!i == input!i1 * input!i2
semanticsAreCorrect m (LDIV p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 && input!i * input!i2 == input!i1
semanticsAreCorrect m (LISZERO p1 w i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 && (input!i * input!i == input!i) &&
                        (input!i1 * input!i == 0) &&
                        (if input!i1 == 0
                         then input!i == 1
                         else input!i == 0 && input!w * input!i1 == 1)
