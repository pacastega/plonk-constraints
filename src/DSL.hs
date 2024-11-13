{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
{-@ LIQUID "--reflection" @-}
module DSL where

import Constraints
import TypeAliases
import ArithmeticGates
import LogicGates
import Circuits

import Utils
import Vec

import qualified Data.Map as M
import Data.IORef
import System.IO.Unsafe

data DSL p where
  -- Basic operations
  DEF   :: String -> DSL p -> DSL p -- variable definition
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
  ISZERO :: DSL p -> DSL p          -- zero check
  EQL    :: DSL p -> DSL p -> DSL p -- equality check
  EQLC   :: DSL p -> p     -> DSL p -- equality check against a constant

  -- Vectors
  NIL  :: DSL p
  CONS :: DSL p -> DSL p -> DSL p

  -- (Non-expression) assertions
  NZERO  :: DSL p -> DSL p -- non-zero assertion
  BOOL   :: DSL p -> DSL p -- booleanity assertion

  deriving (Eq, Ord)

infixr 5 `CONS`


{-@
data DSL p where
  DEF   :: String -> {v:DSL p | unpacked v} -> DSL p
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

  ISZERO :: {v:DSL p | unpacked v} -> DSL p
  EQL    :: {v:DSL p | unpacked v} -> {u:DSL p | unpacked u} -> DSL p
  EQLC   :: {v:DSL p | unpacked v} -> p                      -> DSL p

  NIL  :: DSL p
  CONS :: head:{DSL p | unpacked head} -> tail:{DSL p | isVector tail} -> DSL p

  NZERO  :: {v:DSL p | unpacked v} -> DSL p
  BOOL   :: {v:DSL p | unpacked v} -> DSL p
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

unpacked (DEF _ p)   = unpacked p
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

unpacked (NZERO p)   = unpacked p
unpacked (BOOL p)    = unpacked p

-- Labeled DSL
data LDSL p i =
  LWIRE                          i |

  LVAR   String                  i |
  LCONST p                       i |
  LADD   (LDSL p i) (LDSL p i)   i |
  LSUB   (LDSL p i) (LDSL p i)   i |
  LMUL   (LDSL p i) (LDSL p i)   i |
  LDIV   (LDSL p i) (LDSL p i) i i |

  LNOT   (LDSL p i)            i |
  LAND   (LDSL p i) (LDSL p i) i |
  LOR    (LDSL p i) (LDSL p i) i |
  LXOR   (LDSL p i) (LDSL p i) i |

  LUnsafeNOT   (LDSL p i)            i |
  LUnsafeAND   (LDSL p i) (LDSL p i) i |
  LUnsafeOR    (LDSL p i) (LDSL p i) i |
  LUnsafeXOR   (LDSL p i) (LDSL p i) i |

  LISZERO (LDSL p i)         i i |
  LEQLC   (LDSL p i) p       i i |

  LNZERO  (LDSL p i)           i |
  LBOOL   (LDSL p i)
  deriving Show


type Env p i = M.Map (DSL p) i


{-@ type Store p = [{v:DSL p | unpacked v}] @-}
type Store p = [DSL p]

-- TODO: this could probably be avoided by using record syntax
{-@ measure outputWire @-}
outputWire :: LDSL p i -> i
outputWire (LWIRE i)      = i

outputWire (LVAR _ i)     = i
outputWire (LCONST _ i)   = i
outputWire (LADD _ _ i)   = i
outputWire (LSUB _ _ i)   = i
outputWire (LMUL _ _ i)   = i
outputWire (LDIV _ _ _ i) = i

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

-- assertions
outputWire (LNZERO p w) = outputWire p
outputWire (LBOOL  p)   = outputWire p


-- the number of gates needed to compile the program into a circuit
{-@ measure nGates @-}
{-@ nGates :: LDSL p i -> Nat @-}
nGates :: LDSL p i -> Int
nGates (LWIRE _)        = 0

nGates (LVAR _ _)       = 0
nGates (LCONST _ _)     = 1
nGates (LADD p1 p2 _)   = 1 + nGates p1 + nGates p2
nGates (LSUB p1 p2 _)   = 1 + nGates p1 + nGates p2
nGates (LMUL p1 p2 _)   = 1 + nGates p1 + nGates p2
nGates (LDIV p1 p2 _ _) = 2 + nGates p1 + nGates p2

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

nGates (LNZERO p1 _)    = 1 + nGates p1
nGates (LBOOL p1)       = 1 + nGates p1

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
compile m (LDIV p1 p2 w i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (divGate m [i1, i2, i, w]) c'
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

compile m (LNZERO p1 w) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (nonZeroGate m [i1, w]) c1
compile m (LBOOL p1) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (boolGate m i1) c1


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
semanticsAreCorrect m (LDIV p1 p2 w i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 && input!w * input!i2 == 1 &&
    if input!i2 /= 0 then input!i == input!i1 / input!i2 else True
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
semanticsAreCorrect m (LNZERO p1 w) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 && (input!i1 * input!w == 1)
semanticsAreCorrect m (LBOOL p1) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 && boolean (input!i1)

{-# NOINLINE counter #-}
counter :: IORef Int
counter = unsafePerformIO $ newIORef 0

{-# NOINLINE fresh #-}
fresh :: () -> IO Int
fresh () = (
    do x <- readIORef counter
       writeIORef counter (x+1)
       return x)

var :: String -> String
var name = name ++ "#" ++ show (unsafePerformIO $ fresh ())
