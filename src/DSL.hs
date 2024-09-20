{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-positivity-check" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--max-case-expand=12" @-}
module DSL where

import Constraints
import RefinementTypes()
import ArithmeticGates
import LogicGates
import Circuits

import Utils
import Vec

import qualified Data.Set as S

-- The type variable ‘i’ should be understood as the set of wire indices
data DSL p i t where
  -- Basic operations
  WIRE  :: i -> DSL p i p -- wire (i.e. variable)
  CONST :: p -> DSL p i p -- constant

  -- Arithmetic operations
  ADD :: DSL p i p -> DSL p i p -> DSL p i p -- field addition
  SUB :: DSL p i p -> DSL p i p -> DSL p i p -- field substraction
  MUL :: DSL p i p -> DSL p i p -> DSL p i p -- field multiplication
  DIV :: DSL p i p -> DSL p i p -> DSL p i p -- field division

  -- Boolean operations
  NOT :: DSL p i Bool -> DSL p i Bool                 -- logical not
  AND :: DSL p i Bool -> DSL p i Bool -> DSL p i Bool -- logical and
  OR  :: DSL p i Bool -> DSL p i Bool -> DSL p i Bool -- logical or
  XOR :: DSL p i Bool -> DSL p i Bool -> DSL p i Bool -- logical xor

  -- Boolean constructors
  EQL    :: DSL p i p -> DSL p i p -> DSL p i Bool -- equality check
  ISZERO :: DSL p i p -> DSL p i Bool              -- zero check

  -- Functional constructs: iterators
  ITER :: Bound -> (Int -> DSL p i t -> DSL p i t) -> DSL p i t -> DSL p i t


{-@
data DSL p i t where
  WIRE  :: i -> DSL p i p
  CONST :: p -> DSL p i p

  ADD :: DSL p i p -> DSL p i p -> DSL p i p
  SUB :: DSL p i p -> DSL p i p -> DSL p i p
  MUL :: DSL p i p -> DSL p i p -> DSL p i p
  DIV :: DSL p i p -> DSL p i p -> DSL p i p

  NOT :: DSL p i Bool -> DSL p i Bool
  AND :: DSL p i Bool -> DSL p i Bool -> DSL p i Bool
  OR  :: DSL p i Bool -> DSL p i Bool -> DSL p i Bool
  XOR :: DSL p i Bool -> DSL p i Bool -> DSL p i Bool

  EQL    :: DSL p i p -> DSL p i p -> DSL p i Bool
  ISZERO :: DSL p i p -> DSL p i Bool

  ITER :: b:Bound -> ({v:Int | within b v} -> DSL p i t -> DSL p i t) ->
          DSL p i t -> DSL p i t
@-}


{-@ data Bound = B {s::Int, e::{v:Int | s <= v}} @-}
data Bound = B Int Int

{-@ reflect within @-}
within :: Bound -> Int -> Bool
within (B s e) x = s <= x && x <= e


{-@ measure desugared @-}
desugared :: DSL i p t -> Bool
desugared (EQL {})  = False
desugared (ITER {}) = False

desugared (WIRE _)  = True
desugared (CONST _) = True

desugared (ADD p1 p2) = desugared p1 && desugared p2
desugared (SUB p1 p2) = desugared p1 && desugared p2
desugared (MUL p1 p2) = desugared p1 && desugared p2
desugared (DIV p1 p2) = desugared p1 && desugared p2

desugared (NOT p)     = desugared p
desugared (AND p1 p2) = desugared p1 && desugared p2
desugared (OR  p1 p2) = desugared p1 && desugared p2
desugared (XOR p1 p2) = desugared p1 && desugared p2

desugared (ISZERO p)  = desugared p

{-@ measure getSize @-}
{-@ getSize :: v:{DSL i p t | isIter v} -> Nat @-}
getSize :: DSL p i t -> Int
getSize (ITER (B s e) _ _) = e - s


{-@ measure isIter @-}
isIter :: DSL i p t -> Bool
isIter (ITER {}) = True
isIter _         = False


{-@ unfoldIter :: p:{DSL p i t | isIter p} -> DSL p i t
                  / [getSize p] @-}
unfoldIter :: DSL p i t -> DSL p i t
unfoldIter (ITER (B s e) f a)
  | s == e    = f s a
  | otherwise = unfoldIter (ITER (B (s+1) e) f (f s a))


{-@ lazy desugar @-}
{-@ desugar :: p:DSL p i t -> {v:DSL p i t | desugared v} @-}
desugar :: DSL p i t -> DSL p i t
-- syntactic sugar:
desugar (EQL p1 p2) = ISZERO (SUB (desugar p1) (desugar p2))
desugar p@(ITER {}) = desugar (unfoldIter p)

-- core language instructions:
desugar (ADD p1 p2) = ADD (desugar p1) (desugar p2)
desugar (SUB p1 p2) = SUB (desugar p1) (desugar p2)
desugar (MUL p1 p2) = MUL (desugar p1) (desugar p2)
desugar (DIV p1 p2) = DIV (desugar p1) (desugar p2)

desugar (NOT p)     = NOT (desugar p)
desugar (AND p1 p2) = AND (desugar p1) (desugar p2)
desugar (OR  p1 p2) = OR  (desugar p1) (desugar p2)
desugar (XOR p1 p2) = XOR (desugar p1) (desugar p2)

desugar (ISZERO p)  = ISZERO (desugar p)

desugar (WIRE i)    = WIRE i
desugar (CONST x)   = CONST x


-- Labeled DSL
data LDSL p i =
  LWIRE  i                       |
  LCONST p                     i |
  LADD   (LDSL p i) (LDSL p i) i |
  LSUB   (LDSL p i) (LDSL p i) i |
  LMUL   (LDSL p i) (LDSL p i) i |
  LDIV   (LDSL p i) (LDSL p i) i |

  LNOT   (LDSL p i)            i |
  LAND   (LDSL p i) (LDSL p i) i |
  LOR    (LDSL p i) (LDSL p i) i |
  LXOR   (LDSL p i) (LDSL p i) i |

  LISZERO (LDSL p i)         i i
  deriving Show


{-@ lazy label @-}
-- label each constructor with the index of the wire where its output will be
{-@ label :: m:Nat1 -> {v:DSL p (Btwn 0 m) t | desugared v} ->
             LDSL p (Btwn 0 m) @-}
label :: Int -> DSL p Int t -> LDSL p Int
label m program = fst $ label' program (wires program) where

  -- combinator to label programs with 1 argument that needs recursive labelling
  {-@ label1 :: (LDSL p (Btwn 0 m) -> Btwn 0 m -> LDSL p (Btwn 0 m)) ->
                {v:DSL p (Btwn 0 m) t | desugared v} ->
                Vec (Btwn 0 m) -> (LDSL p (Btwn 0 m), Vec (Btwn 0 m)) @-}
  label1 :: (LDSL p Int -> Int -> LDSL p Int) ->
            DSL p Int t ->
            Vec Int -> (LDSL p Int, Vec Int)
  label1 ctor arg1 usedWires = (ctor arg1' i, is) where
    i = freshIndex m usedWires
    (arg1', is1) = label' arg1 (usedWires `append` singleton i)
    is = singleton i `append` is1

  -- combinator to label programs with 2 arguments that need recursive labelling
  {-@ label2 :: (LDSL p (Btwn 0 m) -> LDSL p (Btwn 0 m) -> Btwn 0 m ->
                        LDSL p (Btwn 0 m)) ->
                {v:DSL p (Btwn 0 m) t | desugared v} ->
                {v:DSL p (Btwn 0 m) t | desugared v} ->
                Vec (Btwn 0 m) -> (LDSL p (Btwn 0 m), Vec (Btwn 0 m)) @-}
  label2 :: (LDSL p Int -> LDSL p Int -> Int -> LDSL p Int) ->
            DSL p Int t -> DSL p Int t ->
            Vec Int -> (LDSL p Int, Vec Int)
  label2 ctor arg1 arg2 usedWires = (ctor arg1' arg2' i, is) where
    i = freshIndex m usedWires
    (arg1', is1) = label' arg1 (usedWires `append` singleton i)
    (arg2', is2) = label' arg2 (usedWires `append` singleton i `append` is1)
    is = singleton i `append` is1 `append` is2

  {-@ label' :: {v:DSL p (Btwn 0 m) t | desugared v} -> Vec (Btwn 0 m) ->
                (LDSL p (Btwn 0 m), Vec (Btwn 0 m)) @-}
  label' :: DSL p Int t -> Vec Int -> (LDSL p Int, Vec Int)
  label' (WIRE i)  _         = (LWIRE i, singleton i)
  label' (CONST x) usedWires = (LCONST x i, singleton i) where
    i = freshIndex m usedWires
  label' (ADD p1 p2) usedWires = label2 LADD p1 p2 usedWires
  label' (SUB p1 p2) usedWires = label2 LSUB p1 p2 usedWires
  label' (MUL p1 p2) usedWires = label2 LMUL p1 p2 usedWires
  label' (DIV p1 p2) usedWires = label2 LDIV p1 p2 usedWires

  label' (NOT p1)    usedWires = label1 LNOT p1    usedWires
  label' (AND p1 p2) usedWires = label2 LAND p1 p2 usedWires
  label' (OR  p1 p2) usedWires = label2 LOR  p1 p2 usedWires
  label' (XOR p1 p2) usedWires = label2 LXOR p1 p2 usedWires

  label' (ISZERO p1) usedWires = (LISZERO p1' w i, is) where
    i = freshIndex m usedWires
    w = freshIndex m (usedWires `append` singleton i)
    (p1', is1) = label' p1 (usedWires `append` fromList [i, w])
    is = singleton i `append` singleton w `append` is1


-- TODO: this could probably be avoided by using record syntax
{-@ reflect outputWire @-}
outputWire :: LDSL p i -> i
outputWire (LWIRE i)    = i
outputWire (LCONST _ i) = i
outputWire (LADD _ _ i) = i
outputWire (LSUB _ _ i) = i
outputWire (LMUL _ _ i) = i
outputWire (LDIV _ _ i) = i

outputWire (LNOT _   i) = i
outputWire (LAND _ _ i) = i
outputWire (LOR  _ _ i) = i
outputWire (LXOR _ _ i) = i

outputWire (LISZERO _ _ i) = i


{-@ wires :: {v:DSL p i t | desugared v} -> Vec i @-}
wires :: DSL p i t -> Vec i
wires (WIRE n)    = singleton n
wires (CONST _)   = Nil
wires (ADD p1 p2) = wires p1 `append` wires p2
wires (SUB p1 p2) = wires p1 `append` wires p2
wires (MUL p1 p2) = wires p1 `append` wires p2
wires (DIV p1 p2) = wires p1 `append` wires p2

wires (NOT p1)    = wires p1
wires (AND p1 p2) = wires p1 `append` wires p2
wires (OR  p1 p2) = wires p1 `append` wires p2
wires (XOR p1 p2) = wires p1 `append` wires p2

wires (EQL p1 p2)  = wires p1 `append` wires p2

wires (ISZERO p1) = wires p1


{-@ reflect lwires @-}
lwires :: Ord i => LDSL p i -> S.Set i
lwires (LWIRE n)      = S.singleton n
lwires (LCONST _ _)   = S.empty
lwires (LADD p1 p2 _) = lwires p1 `S.union` lwires p2
lwires (LSUB p1 p2 _) = lwires p1 `S.union` lwires p2
lwires (LMUL p1 p2 _) = lwires p1 `S.union` lwires p2
lwires (LDIV p1 p2 _) = lwires p1 `S.union` lwires p2

lwires (LNOT p1    _) = lwires p1
lwires (LAND p1 p2 _) = lwires p1 `S.union` lwires p2
lwires (LOR  p1 p2 _) = lwires p1 `S.union` lwires p2
lwires (LXOR p1 p2 _) = lwires p1 `S.union` lwires p2

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
nGates (LSUB p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LMUL p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LDIV p1 p2 _) = 1 + nGates p1 + nGates p2

nGates (LNOT p1    _) = 2 + nGates p1
nGates (LAND p1 p2 _) = 3 + nGates p1 + nGates p2
nGates (LOR  p1 p2 _) = 3 + nGates p1 + nGates p2
nGates (LXOR p1 p2 _) = 3 + nGates p1 + nGates p2

nGates (LISZERO p1 _ _) = 2 + nGates p1


-- compile the program into a circuit including the output wire index
{-@ reflect compile @-}
{-@ compile :: m:Nat ->
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
compile m (LSUB p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (addGate m [i, i2, i1]) c'
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
compile m (LNOT p1 i) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (notGate m [i1, i]) c1
compile m (LAND p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (andGate m [i1, i2, i]) c'
compile m (LOR  p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (orGate m [i1, i2, i]) c'
compile m (LXOR p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (xorGate m [i1, i2, i]) c'
compile m (LISZERO p1 w i) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (isZeroGate m [i1, w, i]) c1


{-@ reflect semanticsAreCorrect @-}
{-@ semanticsAreCorrect :: m:Nat ->
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
semanticsAreCorrect m (LSUB p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 && input!i == input!i1 - input!i2
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
semanticsAreCorrect m (LNOT p1 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 && input!i == 1 - input!i1 && boolean (input!i1)
semanticsAreCorrect m (LAND p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 &&
    (input!i == if input!i1 == 0 || input!i2 == 0 then 0 else 1) &&
    boolean (input!i1) && boolean (input!i2)
semanticsAreCorrect m (LOR  p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 &&
    (input!i == if input!i1 == 1 || input!i2 == 1 then 1 else 0) &&
    boolean (input!i1) && boolean (input!i2)
semanticsAreCorrect m (LXOR p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 &&
    (input!i == if input!i1 /= input!i2 then 1 else 0) &&
    boolean (input!i1) && boolean (input!i2)
semanticsAreCorrect m (LISZERO p1 w i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 && (input!i * input!i == input!i) &&
                        (input!i1 * input!i == 0) &&
                        (if input!i1 == 0
                         then input!i == 1
                         else input!i == 0 && input!w * input!i1 == 1)
