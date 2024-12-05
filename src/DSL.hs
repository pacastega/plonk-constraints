{-# LANGUAGE StandaloneDeriving #-}
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


import Language.Haskell.Liquid.ProofCombinators

-- for use with DataKinds
-- data Ty = TF | TInt32 | TByte | TBool | TVec Ty deriving (Eq, Show)

data DSL p t where
  -- Basic operations
  VAR   :: String -> DSL p t -- variable (the exact type is determined by Γ)
  CONST :: p      -> DSL p p -- constant (of type p, i.e. prime field)
  -- TODO: add constants of other types (integers, booleans...)
  TRUE  :: DSL p Bool
  FALSE :: DSL p Bool

  -- Arithmetic operations
  ADD :: Num t => DSL p t -> DSL p t -> DSL p t        -- addition
  SUB :: Num t => DSL p t -> DSL p t -> DSL p t        -- substraction
  MUL :: Num t => DSL p t -> DSL p t -> DSL p t        -- multiplication
  DIV :: Fractional t => DSL p t -> DSL p t -> DSL p t -- division

  -- Boolean operations
  NOT :: DSL p Bool -> DSL p Bool               -- logical not
  AND :: DSL p Bool -> DSL p Bool -> DSL p Bool -- logical and
  OR  :: DSL p Bool -> DSL p Bool -> DSL p Bool -- logical or
  XOR :: DSL p Bool -> DSL p Bool -> DSL p Bool -- logical xor

  UnsafeNOT :: DSL p Bool -> DSL p Bool               -- unsafe logical not
  UnsafeAND :: DSL p Bool -> DSL p Bool -> DSL p Bool -- unsafe logical and
  UnsafeOR  :: DSL p Bool -> DSL p Bool -> DSL p Bool -- unsafe logical or
  UnsafeXOR :: DSL p Bool -> DSL p Bool -> DSL p Bool -- unsafe logical xor

  -- Boolean constructors
  ISZERO :: DSL p p            -> DSL p Bool -- zero check
  EQL    :: DSL p p -> DSL p p -> DSL p Bool -- equality check
  EQLC   :: DSL p p -> p       -> DSL p Bool -- equality check against constant

  -- Vectors
  NIL  :: DSL p [t]
  CONS :: DSL p t -> DSL p [t] -> DSL p [t]

deriving instance Eq p  => Eq  (DSL p t)
deriving instance Ord p => Ord (DSL p t)

infixr 5 `CONS`

-- (Non-expression) assertions
data Assertion p where
  DEF    :: String  -> DSL p t -> Assertion p -- variable definition
  NZERO  :: DSL p p            -> Assertion p -- non-zero assertion
  BOOL   :: DSL p p            -> Assertion p -- booleanity assertion
  EQA    :: DSL p p -> DSL p p -> Assertion p -- equality assertion

toDSLBool :: Integral a => a -> DSL p Bool
toDSLBool x = if (fromIntegral x == 0) then FALSE else TRUE

{-@
data DSL p t where
  VAR   :: String -> DSL p t
  CONST :: p      -> DSL p p
  TRUE  :: DSL p Bool
  FALSE :: DSL p Bool

  ADD :: {v:DSL p t | scalar v} -> {u:DSL p t | scalar u} -> DSL p t
  SUB :: {v:DSL p t | scalar v} -> {u:DSL p t | scalar u} -> DSL p t
  MUL :: {v:DSL p t | scalar v} -> {u:DSL p t | scalar u} -> DSL p t
  DIV :: {v:DSL p t | scalar v} -> {u:DSL p t | scalar u} -> DSL p t

  NOT :: {v:DSL p Bool | scalar v} ->                              DSL p Bool
  AND :: {v:DSL p Bool | scalar v} -> {u:DSL p Bool | scalar u} -> DSL p Bool
  OR  :: {v:DSL p Bool | scalar v} -> {u:DSL p Bool | scalar u} -> DSL p Bool
  XOR :: {v:DSL p Bool | scalar v} -> {u:DSL p Bool | scalar u} -> DSL p Bool

  UnsafeNOT :: {v:DSL p Bool | scalar v} ->                         DSL p Bool
  UnsafeAND :: {v:DSL p Bool | scalar v} -> {u:DSL p Bool | scalar u} -> DSL p Bool
  UnsafeOR  :: {v:DSL p Bool | scalar v} -> {u:DSL p Bool | scalar u} -> DSL p Bool
  UnsafeXOR :: {v:DSL p Bool | scalar v} -> {u:DSL p Bool | scalar u} -> DSL p Bool

  ISZERO :: {v:DSL p p | scalar v} ->                           DSL p Bool
  EQL    :: {v:DSL p p | scalar v} -> {u:DSL p p | scalar u} -> DSL p Bool
  EQLC   :: {v:DSL p p | scalar v} -> p                      -> DSL p Bool

  NIL  :: DSL _ [t]
  CONS :: DSL _ t -> {tail:DSL _ [t] | vector tail} -> DSL _ [t]
@-}

{-@
data Assertion p where
  DEF    :: String                 -> DSL p t                -> Assertion p
  NZERO  :: {v:DSL p p | scalar v}                           -> Assertion p
  BOOL   :: {v:DSL p p | scalar v}                           -> Assertion p
  EQA    :: {v:DSL p p | scalar v} -> {u:DSL p p | scalar u} -> Assertion p
@-}

{-@ assume isVector :: d:DSL p [t] -> {v:DSL p [t] | vector v && v = d} @-}
isVector :: DSL p [t] -> DSL p [t]
isVector d = d

{- measure vlength @-}
{-@ vlength :: DSL p [t] -> Nat @-}
vlength :: DSL p [t] -> Int
vlength (NIL)       = 0
vlength (CONS _ ps) = 1 + vlength ps
vlength d           = (flip const) (isVector d) (error "undefined")  

{-@ measure scalar @-}
scalar :: DSL p t -> Bool
scalar (NIL)     = False
scalar (CONS {}) = False
scalar _         = True

{-@ measure vector @-}
vector :: DSL p t -> Bool
vector (NIL)     = True
vector (CONS {}) = True
vector _         = False

-- TODO: how to declare variables with type annotations
-- declare :: t:Ty -> String -> {p:DSL p | type p = t}
-- type TyEnv = M.Map String Ty

-- {-@ measure typecheck @-}
-- typecheck :: TyEnv -> DSL p -> Ty -> Bool
-- typecheck γ = check where
--   check :: DSL p -> Ty -> Bool
--   check program τ = case program of
--     VAR s   -> matches (M.lookup γ s) τ
--     CONST _ -> (τ == TF)

--     ADD p1 p2 -> (τ == TF) && (check p1 TF) && (check p2 TF)
--     SUB p1 p2 -> (τ == TF) && (check p1 TF) && (check p2 TF)
--     MUL p1 p2 -> (τ == TF) && (check p1 TF) && (check p2 TF)
--     DIV p1 p2 -> (τ == TF) && (check p1 TF) && (check p2 TF)

--     NOT p1    -> (τ == TBool) && (check p1 TBool)
--     AND p1 p2 -> (τ == TBool) && (check p1 TBool) && (check p2 TBool)
--     OR  p1 p2 -> (τ == TBool) && (check p1 TBool) && (check p2 TBool)
--     XOR p1 p2 -> (τ == TBool) && (check p1 TBool) && (check p2 TBool)

--     UnsafeNOT p1    -> (τ == TBool) && (check p1 TBool)
--     UnsafeAND p1 p2 -> (τ == TBool) && (check p1 TBool) && (check p2 TBool)
--     UnsafeOR  p1 p2 -> (τ == TBool) && (check p1 TBool) && (check p2 TBool)
--     UnsafeXOR p1 p2 -> (τ == TBool) && (check p1 TBool) && (check p2 TBool)

--     EQL p1 p2 -> (τ == TBool) && (check p1 TF) && (check p2 TF)
--     ISZERO p1 -> (τ == TBool) && (check p1 TF)
--     EQLC p1 _ -> (τ == TBool) && (check p1 TF)

--     NIL       -> case τ of
--       Vec _ -> True; otherwise -> False
--     CONS h ts -> case τ of
--       Vec τ' -> (check h τ') && (check ts (Vec τ'))
--       _      -> False

--   matches :: Maybe Ty -> Ty -> Bool
--   matches mτ τ = case mτ of Nothing -> False; Just τ' -> (τ == τ')


type Valuation p = M.Map String p

-- TODO: how to deal with vectors? just forbid them in the precondition?
{-@ eval :: {v:DSL p t | scalar v} -> Valuation p -> Maybe p @-}
eval :: (Fractional p, Eq p) => DSL p t -> Valuation p -> Maybe p
eval program v = case program of
  VAR name -> M.lookup name v
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
