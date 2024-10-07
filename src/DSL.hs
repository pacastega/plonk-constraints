{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-positivity-check" @-}
{-@ LIQUID "--reflection" @-}
module DSL where

import Constraints
import RefinementTypes()
import ArithmeticGates
import LogicGates
import Circuits

import Utils
import Vec

import qualified Data.Map as M

data DSL p where
  -- Basic operations
  VAR   :: String -> DSL p -- variable
  CONST :: p      -> DSL p -- constant

  -- Arithmetic operations
  ADD :: DSL p -> DSL p -> DSL p -- field addition
  SUB :: DSL p -> DSL p -> DSL p -- field substraction
  MUL :: DSL p -> DSL p -> DSL p -- field multiplication
  DIV :: DSL p -> DSL p -> DSL p -- field division

  -- Boolean operations
  NOT :: DSL p -> DSL p          -- logical not
  AND :: DSL p -> DSL p -> DSL p -- logical and
  OR  :: DSL p -> DSL p -> DSL p -- logical or
  XOR :: DSL p -> DSL p -> DSL p -- logical xor

  -- Boolean constructors
  EQL    :: DSL p -> DSL p -> DSL p -- equality check
  ISZERO :: DSL p -> DSL p          -- zero check

  -- Functional constructs: iterators & local bindings
  ITER :: Bound -> (Int -> DSL p -> DSL p) -> DSL p -> DSL p
  LET  :: String -> DSL p -> DSL p -> DSL p

  -- Vectors
  NIL  :: DSL p
  CONS :: DSL p -> DSL p -> DSL p

infixr 5 `CONS`


{-@
data DSL p where
  VAR   :: String -> DSL p
  CONST :: p      -> DSL p

  ADD :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  SUB :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  MUL :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  DIV :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p

  NOT :: {v:DSL p | unpacked v}                           -> DSL p
  AND :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  OR  :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  XOR :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p

  EQL    :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  ISZERO :: {v:DSL p | unpacked v} -> DSL p

  ITER :: b:Bound ->
          ({v:Int | within b v} -> {v:DSL p | unpacked v} ->
              {v:DSL p | unpacked v}) ->
          {v:DSL p | unpacked v} -> {v:DSL p | unpacked v}
  LET  :: String -> {v:DSL p | unpacked v} -> DSL p -> DSL p

  NIL  :: DSL p
  CONS :: head:{DSL p | unpacked head} -> tail:{DSL p | isVector tail} -> DSL p

@-}

{-@ measure vlength @-}
{-@ vlength :: DSL p -> Nat @-}
vlength :: DSL p -> Int
vlength (NIL)       = 0
vlength (CONS _ ps) = 1 + vlength ps
vlength (LET _ _ p) = vlength p
vlength _           = 1

{-@ measure isVector @-}
isVector :: DSL p -> Bool
isVector (NIL)      = True
isVector (CONS _ _) = True
isVector (LET _ _ p) = False --TODO: this should be ‘isVector p’
isVector _          = False

{-@ data Bound = B {s::Int, e::{v:Int | s <= v}} @-}
data Bound = B Int Int

{-@ reflect within @-}
within :: Bound -> Int -> Bool
within (B s e) x = s <= x && x <= e


{-@ measure desugared @-}
desugared :: DSL p -> Bool
desugared (EQL {})  = False
desugared (ITER {}) = False

desugared (LET _ b p) = desugared b && desugared p

desugared (VAR _)   = True
desugared (CONST _) = True

desugared (NIL)       = True
desugared (CONS p ps) = desugared p  && desugared ps

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
{-@ getSize :: v:{DSL p | isIter v} -> Nat @-}
getSize :: DSL p -> Int
getSize (ITER (B s e) _ _) = e - s


{-@ measure isIter @-}
isIter :: DSL p -> Bool
isIter (ITER {}) = True
isIter _         = False


{-@ unfoldIter :: p:{DSL p | isIter p} -> DSL p
                  / [getSize p] @-}
unfoldIter :: DSL p -> DSL p
unfoldIter (ITER (B s e) f a)
  | s == e    = f s a
  | otherwise = unfoldIter (ITER (B (s+1) e) f (f s a))


{-@ lazy desugar @-}
{-@ desugar :: p:DSL p ->
               {v:DSL p | desugared v && (unpacked p => unpacked v)
                                      && (isVector p => isVector v)} @-}
desugar :: DSL p -> DSL p
-- syntactic sugar:
desugar (EQL p1 p2) = ISZERO (SUB (desugar p1) (desugar p2))
desugar p@(ITER {}) = desugar (unfoldIter p)

desugar (LET s b p) = LET s (desugar b) (desugar p)

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

desugar (VAR s)     = VAR s
desugar (CONST x)   = CONST x

desugar (NIL)       = NIL
desugar (CONS p ps) = CONS (desugar p) (desugar ps)


{-@ get :: v:{DSL p | isVector v} -> Btwn 0 (vlength v) -> DSL p @-}
get :: DSL p -> Int -> DSL p
get (CONS p _ ) 0 = p
get (CONS _ ps) i = get ps (i-1)

{-@ set :: v:{DSL p | isVector v} -> Btwn 0 (vlength v) ->
           {x:DSL p | unpacked x} ->
           {u:DSL p | isVector u && vlength u = vlength v} @-}
set :: DSL p -> Int -> DSL p -> DSL p
set (CONS _ ps) 0 x = CONS x ps
set (CONS p ps) i x = CONS p (set ps (i-1) x)


{-@ measure unpacked @-}
{-@ unpacked :: DSL p -> Bool @-}
unpacked :: DSL p -> Bool
unpacked (EQL p1 p2) = unpacked p1 && unpacked p2

unpacked (VAR _)     = True
unpacked (CONST _)   = True

unpacked (NIL)       = False
unpacked (CONS _ _)  = False

unpacked (ADD p1 p2) = unpacked p1 && unpacked p2
unpacked (SUB p1 p2) = unpacked p1 && unpacked p2
unpacked (MUL p1 p2) = unpacked p1 && unpacked p2
unpacked (DIV p1 p2) = unpacked p1 && unpacked p2

unpacked (NOT p)     = unpacked p
unpacked (AND p1 p2) = unpacked p1 && unpacked p2
unpacked (OR  p1 p2) = unpacked p1 && unpacked p2
unpacked (XOR p1 p2) = unpacked p1 && unpacked p2

unpacked (ISZERO p)  = unpacked p
unpacked (LET _ _ p) = False -- gets compiled to a list of more than one program
unpacked (ITER {})   = False


-- Labeled DSL
data LDSL p i =
  LWIRE  String i                |
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


{-@ type Env M = M.Map String (Btwn 0 M) @-}
type Env = M.Map String Int


{-@ lazy label @-}
-- label each constructor with the index of the wire where its output will be
{-@ label :: m:Nat1 -> [{v:DSL p | desugared v}] ->
             ([LDSL p (Btwn 0 m)], Env m) @-}
label :: Int -> [DSL p] -> ([LDSL p Int], Env)
label m programs = (labeledPrograms, finalEnv) where
  (labeledPrograms, _, finalEnv) = labelAll programs

  {-@ labelAll :: [{v:DSL p | desugared v}] ->
                  ([LDSL p (Btwn 0 m)], [Btwn 0 m], Env m) @-}
  labelAll :: [DSL p] -> ([LDSL p Int], [Int], Env)
  labelAll programs = foldl go ([], [], M.empty) programs where
    {-@ go :: ([LDSL p (Btwn 0 m)], [Btwn 0 m], Env m) ->
              {v:DSL p | desugared v} ->
              ([LDSL p (Btwn 0 m)], [Btwn 0 m], Env m) @-}
    go :: ([LDSL p Int], [Int], Env) -> DSL p -> ([LDSL p Int], [Int], Env)
    go (acc, ws, env) program =
      let (labeledProgram, ws', env') = label' program ws env
      in (acc ++ labeledProgram, ws', env')

  -- combinator to label programs with 1 argument that needs recursive labelling
  {-@ label1 :: (LDSL p (Btwn 0 m) -> Btwn 0 m -> LDSL p (Btwn 0 m)) ->
                {arg:DSL p | desugared arg && unpacked arg} ->
                [Btwn 0 m] -> Env m ->
                (ListN (LDSL p (Btwn 0 m)) 1, [Btwn 0 m], Env m) @-}
  label1 :: (LDSL p Int -> Int -> LDSL p Int) ->
            DSL p ->
            [Int] -> Env ->
            ([LDSL p Int], [Int], Env)
  label1 ctor arg1 usedWires env = ([ctor arg1' i], is1, env') where
    i = freshIndex m usedWires
    ([arg1'], is1, env') = label' arg1 (i:usedWires) env

  -- combinator to label programs with 2 arguments that need recursive labelling
  {-@ label2 :: (LDSL p (Btwn 0 m) -> LDSL p (Btwn 0 m) -> Btwn 0 m ->
                        LDSL p (Btwn 0 m)) ->
                {arg1:DSL p | desugared arg1 && unpacked arg1} ->
                {arg2:DSL p | desugared arg2 && unpacked arg2} ->
                [Btwn 0 m] -> Env m ->
                (ListN (LDSL p (Btwn 0 m)) 1, [Btwn 0 m], Env m) @-}
  label2 :: (LDSL p Int -> LDSL p Int -> Int -> LDSL p Int) ->
            DSL p -> DSL p ->
            [Int] -> Env ->
            ([LDSL p Int], [Int], Env)
  label2 ctor arg1 arg2 usedWires env = ([ctor arg1' arg2' i], is2, env'') where
    i = freshIndex m usedWires
    ([arg1'], is1, env') = label' arg1 (i:usedWires) env
    ([arg2'], is2, env'') = label' arg2 is1 env'

  {-@ label' :: program:{DSL p | desugared program} -> [Btwn 0 m] -> Env m ->
                ({l:[LDSL p (Btwn 0 m)] | unpacked program => len l = 1},
                 [Btwn 0 m],
                 Env m) @-}
  label' :: DSL p -> [Int] -> Env -> ([LDSL p Int], [Int], Env)
  label' (VAR s) usedWires env = case M.lookup s env of
      Nothing -> let i = freshIndex m usedWires -- free variable
                 in ([LWIRE s i], i:usedWires, add (s,i) env)
      Just i  -> ([LWIRE s i], usedWires, env)
    where add (k,v) = M.alter (\_ -> Just v) k
  label' (CONST x) usedWires env = ([LCONST x i], i:usedWires, env)
    where i = freshIndex m usedWires
  label' (ADD p1 p2) usedWires env = label2 LADD p1 p2 usedWires env
  label' (SUB p1 p2) usedWires env = label2 LSUB p1 p2 usedWires env
  label' (MUL p1 p2) usedWires env = label2 LMUL p1 p2 usedWires env
  label' (DIV p1 p2) usedWires env = label2 LDIV p1 p2 usedWires env

  label' (NOT p1)    usedWires env = label1 LNOT p1    usedWires env
  label' (AND p1 p2) usedWires env = label2 LAND p1 p2 usedWires env
  label' (OR  p1 p2) usedWires env = label2 LOR  p1 p2 usedWires env
  label' (XOR p1 p2) usedWires env = label2 LXOR p1 p2 usedWires env

  label' (LET var def body) usedWires env =
      let ([def'], ws, env') = label' def usedWires env
          i = outputWire def' -- index of the local definition
          (body', ws', env'') = label' body ws (add (var,i) env')
      in (def':body', ws', recover var env'' env)
      where
        add (k,val) = M.alter (\_ -> Just val) k
        recover k newEnv oldEnv = M.alter (\_ -> M.lookup k oldEnv) k newEnv

  label' (ISZERO p1) usedWires env = ([LISZERO p1' w i], is1, env') where
    i = freshIndex m usedWires
    w = freshIndex m (i:usedWires)
    ([p1'], is1, env') = label' p1 (i:w:usedWires) env

  label' (NIL) usedWires env = ([], usedWires, env)
  label' (CONS p ps) usedWires env = (p' ++ ps', ws', env'') where
    (p', ws, env') = label' p usedWires env
    (ps', ws', env'') = label' ps ws env'

-- TODO: this could probably be avoided by using record syntax
{-@ measure outputWire @-}
outputWire :: LDSL p i -> i
outputWire (LWIRE _ i)  = i
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


-- An upper bound on the number of needed wires (e.g. if some (VAR s) is used
-- more than once in a program, it will be counted once for each appearance).
{-@ measure nWires @-}
{-@ nWires :: {v:DSL p | desugared v} -> Nat @-}
nWires :: DSL p -> Int
nWires (VAR _)     = 1
nWires (CONST _)   = 1

nWires (ADD p1 p2) = 1 + nWires p1 + nWires p2
nWires (SUB p1 p2) = 1 + nWires p1 + nWires p2
nWires (MUL p1 p2) = 1 + nWires p1 + nWires p2
nWires (DIV p1 p2) = 1 + nWires p1 + nWires p2

nWires (NOT p1   ) = 1 + nWires p1
nWires (AND p1 p2) = 1 + nWires p1 + nWires p2
nWires (OR  p1 p2) = 1 + nWires p1 + nWires p2
nWires (XOR p1 p2) = 1 + nWires p1 + nWires p2

nWires (ISZERO p1) = 2 + nWires p1
nWires (LET _ p1 p2) = nWires p1 + nWires p2

nWires (NIL)       = 0
nWires (CONS p ps) = nWires p + nWires ps

{-@ assume enumFromTo :: x:a -> y:a -> [{v:a | x <= v && v <= y}] @-}
-- find a wire index that has not been used yet

{-@ lazy freshIndex @-}
{-@ freshIndex :: m:Nat1 -> [Int] -> Btwn 0 m @-}
freshIndex :: Int -> [Int] -> Int
freshIndex m used = freshIndex_ [0..m-1] where
  {-@ freshIndex_ :: [Btwn 0 m] -> Btwn 0 m @-}
  freshIndex_ []     = 0 -- FIXME: This shouldn’t be reached. How to prove it?
  freshIndex_ (x:xs) = if x `elem` used then freshIndex_ xs else x


-- the number of gates needed to compile the program into a circuit
{-@ measure nGates @-}
{-@ nGates :: LDSL p i -> Nat @-}
nGates :: LDSL p i -> Int
nGates (LWIRE _ _)    = 0
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
compile m (LWIRE _ _)    = emptyCircuit m
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
semanticsAreCorrect _ (LWIRE _ _)    _     = True
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
