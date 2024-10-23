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

  UnsafeNOT :: DSL p -> DSL p          -- unsafe logical not
  UnsafeAND :: DSL p -> DSL p -> DSL p -- unsafe logical and
  UnsafeOR  :: DSL p -> DSL p -> DSL p -- unsafe logical or
  UnsafeXOR :: DSL p -> DSL p -> DSL p -- unsafe logical xor

  -- Boolean constructors
  EQL    :: DSL p -> DSL p -> DSL p -- equality check
  ISZERO :: DSL p -> DSL p          -- zero check
  EQLC   :: DSL p -> p     -> DSL p -- equality check against a constant

  -- Vectors
  NIL  :: DSL p
  CONS :: DSL p -> DSL p -> DSL p
  deriving (Eq, Ord)

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

  UnsafeNOT :: {v:DSL p | unpacked v} -> DSL p
  UnsafeAND :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  UnsafeOR  :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  UnsafeXOR :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p

  EQL    :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  ISZERO :: {v:DSL p | unpacked v} -> DSL p
  EQLC   :: {v:DSL p | unpacked v} -> p                      -> DSL p

  NIL  :: DSL p
  CONS :: head:{DSL p | unpacked head} -> tail:{DSL p | isVector tail} -> DSL p

@-}

{-@ measure vlength @-}
{-@ vlength :: DSL p -> Nat @-}
vlength :: DSL p -> Int
vlength (NIL)       = 0
vlength (CONS _ ps) = 1 + vlength ps
vlength _           = 1

{-@ measure isVector @-} -- TODO: this should use types
isVector :: DSL p -> Bool
isVector (NIL)      = True
isVector (CONS _ _) = True
isVector _          = False


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

unpacked (UnsafeNOT p)     = unpacked p
unpacked (UnsafeAND p1 p2) = unpacked p1 && unpacked p2
unpacked (UnsafeOR  p1 p2) = unpacked p1 && unpacked p2
unpacked (UnsafeXOR p1 p2) = unpacked p1 && unpacked p2

unpacked (ISZERO p)  = unpacked p
unpacked (EQLC p _)  = unpacked p


-- Labeled DSL
data LDSL p i =
  LWIRE                        i |

  LVAR   String                i |
  LCONST p                     i |
  LADD   (LDSL p i) (LDSL p i) i |
  LSUB   (LDSL p i) (LDSL p i) i |
  LMUL   (LDSL p i) (LDSL p i) i |
  LDIV   (LDSL p i) (LDSL p i) i |

  LNOT   (LDSL p i)            i |
  LAND   (LDSL p i) (LDSL p i) i |
  LOR    (LDSL p i) (LDSL p i) i |
  LXOR   (LDSL p i) (LDSL p i) i |

  LUnsafeNOT   (LDSL p i)            i |
  LUnsafeAND   (LDSL p i) (LDSL p i) i |
  LUnsafeOR    (LDSL p i) (LDSL p i) i |
  LUnsafeXOR   (LDSL p i) (LDSL p i) i |

  LISZERO (LDSL p i)         i i |
  LEQLC   (LDSL p i) p       i i
  deriving Show


type Env p i = M.Map (DSL p) i


{-@ lazy label @-}
-- label each constructor with the index of the wire where its output will be
{-@ label :: [DSL p] ->
             (m:Nat, [LDSL p Int])<\m -> {l:[LDSL p (Btwn 0 m)] | true}> @-}
label :: Ord p => [DSL p] -> (Int, [LDSL p Int])
label programs = (m, labeledPrograms) where
  (m, labeledPrograms, _) = labelAll programs

  {-@ labelAll :: [DSL p] ->
                  (m:Nat, [LDSL p Int], Env p Int)
                             <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                              \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
  labelAll :: Ord p => [DSL p] -> (Int, [LDSL p Int], Env p Int)
  labelAll programs = foldl go (0, [], M.empty) programs where
    {-@ go :: (m:Nat, [LDSL p Int], Env p Int)
                            <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                             \_ m -> {v:Env   p (Btwn 0 m)  | true}>
           -> DSL p
           -> (m:Nat, [LDSL p Int], Env p Int)
                            <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                             \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
    go :: Ord p =>
          (Int, [LDSL p Int], Env p Int) -> DSL p ->
          (Int, [LDSL p Int], Env p Int)
    go (nextIndex, acc, env) program =
      let (nextIndex', labeledProgram, env') = label' program nextIndex env
      in (nextIndex', acc ++ labeledProgram, env')

  -- combinator to label programs with 2 arguments that need recursive labelling
  {-@ label2 :: m0:Nat ->
                {arg1:DSL p | unpacked arg1} ->
                {arg2:DSL p | unpacked arg2} ->
                Env p (Btwn 0 m0) ->
                (m:{Int | m >= m0}, LDSL p Int, LDSL p Int, Env p Int)
                           <\m     -> {v:LDSL  p (Btwn 0 m)  | true},
                            \_ m   -> {v:LDSL  p (Btwn 0 m)  | true},
                            \_ _ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
  label2 :: Ord p => Int -> DSL p -> DSL p -> Env p Int ->
            (Int, LDSL p Int, LDSL p Int, Env p Int)
  label2 nextIndex arg1 arg2 env =
    let i = nextIndex
        (i1, [arg1'], env1) = label' arg1 i  env
        (i2, [arg2'], env2) = label' arg2 i1 env1
    in (i2, arg1', arg2', env2)

  add (k,v) = M.alter (\_ -> Just v) k

  {-@ label' :: program:(DSL p) ->
                m0:Nat -> Env p (Btwn 0 m0) ->
                (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
             <\m   -> {l:[LDSL p (Btwn 0 m)] | unpacked program => len l = 1},
              \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
  label' :: Ord p => DSL p -> Int -> Env p Int
         -> (Int, [LDSL p Int], Env p Int)
  label' p nextIndex env = case M.lookup p env of
    Just i  -> (nextIndex, [LWIRE i], env)
    Nothing -> let i = nextIndex in case p of

      VAR s -> (i+1, [LVAR s i], add (p,i) env)
      CONST x -> (i+1, [LCONST x i], add (p,i) env)

      ADD p1 p2 -> (i'+1, [LADD p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      SUB p1 p2 -> (i'+1, [LSUB p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      MUL p1 p2 -> (i'+1, [LMUL p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      DIV p1 p2 -> (i'+1, [LDIV p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env

      NOT p1    -> (i'+1, [LNOT p1' i'], add (p,i') env')
        where (i', [p1'], env') = label' p1 (i+1) env
      AND p1 p2 -> (i'+1, [LAND p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      OR  p1 p2 -> (i'+1, [LOR  p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      XOR p1 p2 -> (i'+1, [LXOR p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env

      UnsafeNOT p1    -> (i'+1, [LUnsafeNOT p1' i'], add (p,i') env')
        where (i', [p1'], env') = label' p1 (i+1) env
      UnsafeAND p1 p2 -> (i'+1, [LUnsafeAND p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      UnsafeOR  p1 p2 -> (i'+1, [LUnsafeOR  p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env
      UnsafeXOR p1 p2 -> (i'+1, [LUnsafeXOR p1' p2' i'], add (p,i') env')
        where (i', p1', p2', env') = label2 i p1 p2 env

      EQL p1 p2 -> label' (ISZERO (p1 `SUB` p2)) nextIndex env
      ISZERO p1 -> (w'+1, [LISZERO p1' w' i'], add (p,i') env')
        where (i', [p1'], env') = label' p1 i env; w' = i'+1
      EQLC p1 k -> (w'+1, [LEQLC p1' k w' i'], add (p,i') env')
        where (i', [p1'], env') = label' p1 i env; w' = i'+1

      NIL -> (i, [], env)
      CONS h ts -> (i'', h' ++ ts', env'')
        where (i',  h',  env')  = label' h  i  env
              (i'', ts', env'') = label' ts i' env'

-- TODO: this could probably be avoided by using record syntax
{-@ measure outputWire @-}
outputWire :: LDSL p i -> i
outputWire (LWIRE i)    = i

outputWire (LVAR _ i)   = i
outputWire (LCONST _ i) = i
outputWire (LADD _ _ i) = i
outputWire (LSUB _ _ i) = i
outputWire (LMUL _ _ i) = i
outputWire (LDIV _ _ i) = i

outputWire (LNOT _   i) = i
outputWire (LAND _ _ i) = i
outputWire (LOR  _ _ i) = i
outputWire (LXOR _ _ i) = i

outputWire (LUnsafeNOT _   i) = i
outputWire (LUnsafeAND _ _ i) = i
outputWire (LUnsafeOR  _ _ i) = i
outputWire (LUnsafeXOR _ _ i) = i

outputWire (LISZERO _ _ i) = i
outputWire (LEQLC _ _ _ i) = i


-- An upper bound on the number of needed wires (e.g. if some (VAR s) is used
-- more than once in a program, it will be counted once for each appearance).
{-@ measure nWires @-}
{-@ nWires :: DSL p -> Nat @-}
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

nWires (UnsafeNOT p1   ) = 1 + nWires p1
nWires (UnsafeAND p1 p2) = 1 + nWires p1 + nWires p2
nWires (UnsafeOR  p1 p2) = 1 + nWires p1 + nWires p2
nWires (UnsafeXOR p1 p2) = 1 + nWires p1 + nWires p2

nWires (EQL p1 p2) = 3 + nWires p1 + nWires p2
nWires (ISZERO p1) = 2 + nWires p1
nWires (EQLC p1 _) = 2 + nWires p1

nWires (NIL)       = 0
nWires (CONS p ps) = nWires p + nWires ps


-- the number of gates needed to compile the program into a circuit
{-@ measure nGates @-}
{-@ nGates :: LDSL p i -> Nat @-}
nGates :: LDSL p i -> Int
nGates (LWIRE _)      = 0

nGates (LVAR _ _)     = 0
nGates (LCONST _ _)   = 1
nGates (LADD p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LSUB p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LMUL p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LDIV p1 p2 _) = 1 + nGates p1 + nGates p2

nGates (LNOT p1    _) = 2 + nGates p1
nGates (LAND p1 p2 _) = 3 + nGates p1 + nGates p2
nGates (LOR  p1 p2 _) = 3 + nGates p1 + nGates p2
nGates (LXOR p1 p2 _) = 3 + nGates p1 + nGates p2

nGates (LUnsafeNOT p1    _) = 1 + nGates p1
nGates (LUnsafeAND p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LUnsafeOR  p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LUnsafeXOR p1 p2 _) = 1 + nGates p1 + nGates p2

nGates (LISZERO p1 _ _) = 2 + nGates p1
nGates (LEQLC p1 _ _ _) = 2 + nGates p1


-- compile the program into a circuit including the output wire index
{-@ reflect compile @-}
{-@ compile :: m:Nat ->
               c:LDSL p (Btwn 0 m) ->
               Circuit p (nGates c) m @-}
compile :: Fractional p => Int -> LDSL p Int -> Circuit p
compile m (LWIRE _)      = emptyCircuit m
compile m (LVAR _ _)     = emptyCircuit m
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
compile m (LUnsafeNOT p1 i) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (unsafeNotGate m [i1, i]) c1
compile m (LUnsafeAND p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (unsafeAndGate m [i1, i2, i]) c'
compile m (LUnsafeOR  p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (unsafeOrGate m [i1, i2, i]) c'
compile m (LUnsafeXOR p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (unsafeXorGate m [i1, i2, i]) c'
compile m (LISZERO p1 w i) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (isZeroGate m [i1, w, i]) c1
compile m (LEQLC p1 k w i) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (isEqlCGate m k [i1, w, i]) c1


{-@ reflect semanticsAreCorrect @-}
{-@ semanticsAreCorrect :: m:Nat ->
                           LDSL p (Btwn 0 m) -> VecN p m ->
                           Bool @-}
semanticsAreCorrect :: (Eq p, Fractional p) => Int -> LDSL p Int -> Vec p -> Bool
semanticsAreCorrect _ (LWIRE _)      _     = True
semanticsAreCorrect _ (LVAR _ _)     _     = True
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
  correct = correct1 &&
    (input!i == if input!i1 == 1 then 0 else 1) &&
    boolean (input!i1)
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
semanticsAreCorrect m (LUnsafeNOT p1 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 &&
    (input!i == 1 - input!i1)
semanticsAreCorrect m (LUnsafeAND p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 &&
    (input!i == input!i1 * input!i2)
semanticsAreCorrect m (LUnsafeOR  p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 &&
    (input!i == input!i1 + input!i2 - input!i1*input!i2)
semanticsAreCorrect m (LUnsafeXOR p1 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 &&
    (input!i == input!i1 + input!i2 - 2*input!i1*input!i2)
semanticsAreCorrect m (LISZERO p1 w i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 && boolean (input!i) &&
                        (input!i1 * input!i == 0) &&
                        (if input!i1 == 0
                         then input!i == 1
                         else input!i == 0 && input!w * input!i1 == 1)
semanticsAreCorrect m (LEQLC p1 k w i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 && boolean (input!i) &&
                        ((input!i1 - k) * input!i == 0) &&
                        (if input!i1 == k
                         then input!i == 1
                         else input!i == 0 && input!w * (input!i1 - k) == 1)
