{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

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

data Ty = TF | TInt32 | TByte | TBool | TVec Ty deriving (Eq, Ord, Show)
{-@ type ScalarTy = {τ:Ty | scalarType τ} @-}

{-@ measure scalarType @-}
scalarType :: Ty -> Bool
scalarType (TVec _) = False
scalarType _        = True


data DSL p =
    -- Basic operations
    VAR String Ty -- variable
  | CONST p       -- constant (of type p, i.e. prime field)
    -- TODO: add constants of other types (integers, booleans...)
  | TRUE
  | FALSE

    -- Arithmetic operations
  | ADD (DSL p) (DSL p) -- addition
  | SUB (DSL p) (DSL p) -- substraction
  | MUL (DSL p) (DSL p) -- multiplication
  | DIV (DSL p) (DSL p) -- division

    -- Boolean operations
  | NOT (DSL p)         -- logical not
  | AND (DSL p) (DSL p) -- logical and
  | OR  (DSL p) (DSL p) -- logical or
  | XOR (DSL p) (DSL p) -- logical xor

  | UnsafeNOT (DSL p)         -- unsafe logical not
  | UnsafeAND (DSL p) (DSL p) -- unsafe logical and
  | UnsafeOR  (DSL p) (DSL p) -- unsafe logical or
  | UnsafeXOR (DSL p) (DSL p) -- unsafe logical xor

    -- Boolean constructors
  | ISZERO (DSL p)         -- zero check
  | EQL    (DSL p) (DSL p) -- equality check
  | EQLC   (DSL p) p       -- equality check against constant

    -- Vectors
  | NIL Ty
  | CONS (DSL p) (DSL p)
  deriving (Eq, Ord)

infixr 5 `CONS`


{-@ measure vlength @-}
{-@ vlength :: DSL p -> Nat @-}
vlength :: DSL p -> Int
vlength (NIL _)     = 0
vlength (CONS _ ps) = 1 + vlength ps
vlength _           = 1

{-@ toDSLBool :: a -> {v:DSL p | typed v TBool} @-}
toDSLBool :: Integral a => a -> DSL p
toDSLBool x = if (fromIntegral x == 0) then FALSE else TRUE


{-@ reflect typed @-}
typed :: DSL p -> Ty -> Bool
typed p τ = inferType p == Just τ

{-@ type ScalarDSL p = {d:DSL p | scalar d} @-}
{-@ type TypedDSL p = {d:DSL p | wellTyped d} @-}

{-@ reflect wellTyped @-}
wellTyped :: DSL p -> Bool
wellTyped p = case inferType p of
  Just _ -> True
  Nothing -> False

{-@ reflect scalar @-}
scalar :: DSL p -> Bool
scalar p = case inferType p of
  Just (TVec _) -> False
  Just _        -> True
  otherwise     -> False


{-@ measure inferType @-}
{-@ inferType :: d:DSL p -> Maybe Ty @-}
inferType :: DSL p -> Maybe Ty
-- TODO: allow vector variables
inferType (VAR _ τ) = if scalarType τ then Just τ else Nothing
inferType (CONST _) = Just TF
inferType (TRUE)    = Just TBool
inferType (FALSE)   = Just TBool

inferType (ADD p1 p2) = if inferType p1 == Just TF && inferType p2 == Just TF
                        then Just TF else Nothing
inferType (SUB p1 p2) = if inferType p1 == Just TF && inferType p2 == Just TF
                        then Just TF else Nothing
inferType (MUL p1 p2) = if inferType p1 == Just TF && inferType p2 == Just TF
                        then Just TF else Nothing
inferType (DIV p1 p2) = if inferType p1 == Just TF && inferType p2 == Just TF
                        then Just TF else Nothing

inferType (NOT p1)    = if inferType p1 == Just TBool
                        then Just TBool else Nothing
inferType (AND p1 p2) = if inferType p1 == Just TBool
                        && inferType p2 == Just TBool
                        then Just TBool else Nothing
inferType (OR  p1 p2) = if inferType p1 == Just TBool
                        && inferType p2 == Just TBool
                        then Just TBool else Nothing
inferType (XOR p1 p2) = if inferType p1 == Just TBool
                        && inferType p2 == Just TBool
                        then Just TBool else Nothing

inferType (UnsafeNOT p1)    = if inferType p1 == Just TBool
                              then Just TBool else Nothing
inferType (UnsafeAND p1 p2) = if inferType p1 == Just TBool
                              && inferType p2 == Just TBool
                              then Just TBool else Nothing
inferType (UnsafeOR  p1 p2) = if inferType p1 == Just TBool
                              && inferType p2 == Just TBool
                              then Just TBool else Nothing
inferType (UnsafeXOR p1 p2) = if inferType p1 == Just TBool
                              && inferType p2 == Just TBool
                              then Just TBool else Nothing

inferType (EQL p1 p2) = if inferType p1 == Just TF && inferType p2 == Just TF
                        then Just TBool else Nothing
inferType (ISZERO p1) = if inferType p1 == Just TF
                        then Just TBool else Nothing
inferType (EQLC p1 _) = if inferType p1 == Just TF
                        then Just TBool else Nothing

inferType (NIL τ) = Just (TVec τ)
inferType (CONS h ts)
  | Just τ  <- inferType h
  , Just τs <- inferType ts
  , τs == TVec τ
  = Just τs
  | otherwise = Nothing


-- (Non-expression) assertions
data Assertion p =
    DEF   String  (DSL p) -- variable definition
  | NZERO (DSL p)         -- non-zero assertion
  | BOOL  (DSL p)         -- booleanity assertion
  | EQA   (DSL p) (DSL p) -- equality assertion

{-@
data Assertion p =
    DEF   String        (ScalarDSL p)
  | NZERO (ScalarDSL p)
  | BOOL  (ScalarDSL p)
  | EQA   (ScalarDSL p) (ScalarDSL p)
@-}


type Valuation p = M.Map String p

-- TODO: how to deal with vectors? just forbid them in the precondition?
{-@ eval :: {v:DSL p | scalar v} -> Valuation p -> Maybe p @-}
eval :: (Fractional p, Eq p) => DSL p -> Valuation p -> Maybe p
eval program v = case program of
  VAR name _ -> M.lookup name v
  CONST x  -> Just x
  TRUE     -> Just 1
  FALSE    -> Just 0

  -- Arithmetic operations
  ADD p1 p2 -> (+) <$> eval p1 v <*> eval p2 v
  SUB p1 p2 -> (-) <$> eval p1 v <*> eval p2 v
  MUL p1 p2 -> (*) <$> eval p1 v <*> eval p2 v
  DIV p1 p2 -> (/) <$> eval p1 v <*> (eval p2 v >>= \x ->
                                     if x /= 0 then Just x else Nothing)

  -- Boolean operations (assume inputs are binary)
  NOT p1    -> (\x -> if x == 1 then 0 else 1) <$> eval p1 v
  AND p1 p2 -> (\x y -> if x == 0 || y == 0 then 0 else 1)
               <$> eval p1 v <*> eval p2 v
  OR  p1 p2 -> (\x y -> if x == 1 || y == 1 then 1 else 0)
               <$> eval p1 v <*> eval p2 v
  XOR p1 p2 -> (\x y -> if x /= y then 1 else 0)
               <$> eval p1 v <*> eval p2 v

  UnsafeNOT p1    -> (\x -> if x == 1 then 0 else 1) <$> eval p1 v
  UnsafeAND p1 p2 -> (\x y -> if x == 0 || y == 0 then 0 else 1)
                     <$> eval p1 v <*> eval p2 v
  UnsafeOR  p1 p2 -> (\x y -> if x == 1 || y == 1 then 1 else 0)
                     <$> eval p1 v <*> eval p2 v
  UnsafeXOR p1 p2 -> (\x y -> if x /= y then 1 else 0)
                     <$> eval p1 v <*> eval p2 v

  ISZERO p1 -> (\x -> if x == 0 then 1 else 0) <$> eval p1 v
  EQL p1 p2 -> (\x y -> if x == y then 1 else 0)
                <$> eval p1 v <*> eval p2 v
  EQLC p1 y -> (\x -> if x == y then 1 else 0) <$> eval p1 v


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
  LBOOL   (LDSL p i)             |
  LEQA    (LDSL p i) (LDSL p i)
  deriving Show


type Store p = [Assertion p]

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
outputWire (LEQA p1 p2) = outputWire p2 --FIXME: assertions don't have output


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
nGates (LEQA p1 p2)     = 1 + nGates p1 + nGates p2

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
compile m (LEQA p1 p2) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (equalGate m [i1, i2]) c'


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
semanticsAreCorrect m (LEQA p1 p2) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 && (input!i1 == input!i2)

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
var name = name ++ "_" ++ show (unsafePerformIO $ fresh ())

{-@ vars :: n:Nat -> String -> ListN String n @-}
vars :: Int -> String -> [String]
vars 0 name = []
vars n name = var name : vars (n-1) name
