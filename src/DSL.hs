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

import Language.Haskell.Liquid.ProofCombinators

data Ty = TF | TBit | TBool | TVec Ty deriving (Eq, Ord, Show)
{-@ type ScalarTy = {τ:Ty | scalarType τ} @-}

{-@ measure scalarType @-}
scalarType :: Ty -> Bool
scalarType TF       = True
scalarType TBit     = True
scalarType TBool    = True
scalarType (TVec _) = False


{-@ measure numericType @-}
numericType :: Ty -> Bool
numericType TF       = True
numericType TBit     = True
numericType TBool    = False
numericType (TVec _) = False


{-@ measure logicType @-}
logicType :: Ty -> Bool
logicType TBit     = True
logicType TBool    = True
logicType TF       = False
logicType (TVec _) = False


data DSL p =
    -- Basic operations
    VAR String Ty -- variable
  | CONST p       -- constant (of type p, i.e. prime field)
    -- TODO: add constants of other types (integers, booleans...)
  | BOOLEAN Bool

    -- Arithmetic operations
  | ADD (DSL p) (DSL p) -- addition
  | SUB (DSL p) (DSL p) -- subtraction
  | MUL (DSL p) (DSL p) -- multiplication
  | DIV (DSL p) (DSL p) -- division

  | LINCOMB p (DSL p) p (DSL p) -- LINCOMB k1 p1 k2 p2 = k1*p1 + k2*p2

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
  deriving (Show, Eq, Ord)

infixr 5 `CONS`


{-@ measure vlength @-}
{-@ vlength :: DSL p -> Nat @-}
vlength :: DSL p -> Int
vlength (NIL _)     = 0
vlength (CONS _ ps) = 1 + vlength ps
vlength _           = 1

{-@ toDSLBool :: a -> {v:DSL p | typed v TBool} @-}
toDSLBool :: Integral a => a -> DSL p
toDSLBool x = if (fromIntegral x == 0) then BOOLEAN False else BOOLEAN True


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
  Nothing       -> False
  Just (TVec _) -> False
  Just _        -> True


{-@ measure inferType @-}
inferType :: DSL p -> Maybe Ty
-- TODO: allow vector variables
inferType (VAR _ τ) | scalarType τ = Just τ
inferType (CONST _) = Just TF
inferType (BOOLEAN _) = Just TBool

inferType (ADD p1 p2) | any' numericType (inferType p1)
                      , any' numericType (inferType p2) = Just TF
inferType (SUB p1 p2) | any' numericType (inferType p1)
                      , any' numericType (inferType p2) = Just TF
inferType (MUL p1 p2) | any' numericType (inferType p1)
                      , any' numericType (inferType p2) = Just TF
inferType (DIV p1 p2) | any' numericType (inferType p1)
                      , any' numericType (inferType p2) = Just TF

inferType (LINCOMB _ p1 _ p2) | any' numericType (inferType p1)
                              , any' numericType (inferType p2) = Just TF

inferType (NOT p1)    | Just τ1 <- inferType p1, logicType τ1 = Just τ1
inferType (AND p1 p2) | Just τ1 <- inferType p1, Just τ2 <- inferType p2
                      , τ1 == τ2, logicType τ1 = Just τ1
inferType (OR  p1 p2) | Just τ1 <- inferType p1, Just τ2 <- inferType p2
                      , τ1 == τ2, logicType τ1 = Just τ1
inferType (XOR p1 p2) | Just τ1 <- inferType p1, Just τ2 <- inferType p2
                      , τ1 == τ2, logicType τ1 = Just τ1

inferType (UnsafeNOT p1)    | Just τ1 <- inferType p1, logicType τ1 = Just τ1
inferType (UnsafeAND p1 p2) | Just τ1 <- inferType p1, Just τ2 <- inferType p2
                            , τ1 == τ2, logicType τ1 = Just τ1
inferType (UnsafeOR  p1 p2) | Just τ1 <- inferType p1, Just τ2 <- inferType p2
                            , τ1 == τ2, logicType τ1 = Just τ1
inferType (UnsafeXOR p1 p2) | Just τ1 <- inferType p1, Just τ2 <- inferType p2
                            , τ1 == τ2, logicType τ1 = Just τ1

inferType (EQL p1 p2) | any' scalarType (inferType p1)
                      , any' scalarType (inferType p2) = Just TBool
inferType (ISZERO p1) | any' scalarType (inferType p1) = Just TBool
inferType (EQLC p1 _) | any' scalarType (inferType p1) = Just TBool

inferType (NIL τ) = Just (TVec τ)
inferType (CONS h ts) | Just τ  <- inferType h
                      , Just τs <- inferType ts
                      , τs == TVec τ = Just τs
inferType _ = Nothing


-- (Non-expression) assertions
data Assertion p =
    DEF   String  (DSL p) Ty -- variable definition
  | NZERO (DSL p)            -- non-zero assertion
  | BOOL  (DSL p)            -- booleanity assertion
  | EQA   (DSL p) (DSL p)    -- equality assertion
  deriving Show

{-@
data Assertion p =
    DEF   String        (ScalarDSL p) ScalarTy
  | NZERO (ScalarDSL p)
  | BOOL  (ScalarDSL p)
  | EQA   (ScalarDSL p) (ScalarDSL p)
@-}


type Valuation p = M.Map String p


{-@ lemmaNum :: d:{DSL p | any' numericType (inferType d)} -> {scalar d} @-}
lemmaNum :: DSL p -> Proof
lemmaNum p = case inferType p of
  Nothing       -> error "unreachable"
  Just (TVec _) -> error "unreachable"
  Just _        -> trivial

{-@ lemmaLogic :: d:{DSL p | any' logicType (inferType d)} -> {scalar d} @-}
lemmaLogic :: DSL p -> Proof
lemmaLogic p = case inferType p of
  Nothing       -> error "unreachable"
  Just (TVec _) -> error "unreachable"
  Just _        -> trivial


-- TODO: how to deal with vectors? just forbid them in the precondition?
{-@ eval :: {v:DSL p | scalar v} -> Valuation p -> Maybe p @-}
eval :: (Fractional p, Eq p) => DSL p -> Valuation p -> Maybe p
eval program v = case program of
  VAR name _ -> M.lookup name v
  CONST x  -> Just x
  (BOOLEAN True) -> Just 1
  (BOOLEAN False) -> Just 0

  -- Arithmetic operations
  ADD p1 p2 -> (+) <$> (eval p1 v ? lemmaNum p1) <*> (eval p2 v ? lemmaNum p2)
  SUB p1 p2 -> ((-) <$> eval p1 v <*> eval p2 v) ? lemmaNum p1 ? lemmaNum p2
  MUL p1 p2 -> (*) <$> eval p1 v <*> eval p2 v ? lemmaNum p1 ? lemmaNum p2
  DIV p1 p2 -> (/) <$> eval p1 v <*> (eval p2 v >>= \x ->
                                     if x /= 0 then Just x else Nothing)
    ? lemmaNum p1 ? lemmaNum p2
  LINCOMB k1 p1 k2 p2 -> (\x y -> k1*x + k2*y) <$> eval p1 v <*> eval p2 v
    ? lemmaNum p1 ? lemmaNum p2
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

  LLINCOMB p (LDSL p i) p (LDSL p i) i |

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
outputWire (LLINCOMB _ _ _ _ i) = i

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

nGates (LLINCOMB _ p1 _ p2 _) = 1 + nGates p1 + nGates p2

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
compile :: (Fractional p, Eq p) => Int -> LDSL p Int -> Circuit p
compile m (LWIRE _)      = emptyCircuit m
compile m (LVAR _ _)     = emptyCircuit m
compile m (LCONST x i)   = constGate m x i
compile m (LADD p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (addGate m [i1, i2, i]) c'
-- -- TODO: is it worth it to add a new DSL constructor (+ LDSL constructor) to
-- -- have this optimization on DSL's instead of LDSL's? (and in MUL as well)
-- compile m (LADD p1 (LCONST k _) i) = c
--   where
--     c1 = compile m p1
--     i1 = outputWire p1
--     c = append' (addGateConst m k [i1, i]) c1
-- compile m (LADD (LCONST k _) p1 i) = c
--   where
--     c1 = compile m p1
--     i1 = outputWire p1
--     c = append' (addGateConst m k [i1, i]) c1
-- compile m (LSUB p1 (LCONST k _) i) = c -- subtract a constant
--   where
--     c1 = compile m p1
--     i1 = outputWire p1
--     c = append' (addGateConst m k [i, i1]) c1
compile m (LSUB p1 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (addGate m [i, i2, i1]) c'
-- compile m (LMUL p1 (LCONST k _) i) = c -- multiply by a constant
--   where
--     c1 = compile m p1
--     i1 = outputWire p1
--     c = append' (mulGateConst m k [i1, i]) c1
-- compile m (LMUL (LCONST k _) p1 i) = c -- multiply by a constant
--   where
--     c1 = compile m p1
--     i1 = outputWire p1
--     c = append' (mulGateConst m k [i1, i]) c1
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
compile m (LLINCOMB k1 p1 k2 p2 i) = c
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (linCombGate m [k1, k2] [i1, i2, i]) c'
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
semanticsAreCorrect m (LLINCOMB k1 p1 k2 p2 i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 && input!i == k1*input!i1 + k2*input!i2
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
