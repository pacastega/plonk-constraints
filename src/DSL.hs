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

data Ty = TF | TBool | TVec Ty Int deriving (Eq, Ord, Show)
{-@ data Ty = TF | TBool | TVec Ty Nat @-}
{-@ type ScalarTy = {τ:Ty | scalarType τ} @-}

{-@ measure scalarType @-}
scalarType :: Ty -> Bool
scalarType TF       = True
scalarType TBool    = True
scalarType TVec {}  = False


data DSL p =
    -- Basic operations
    VAR String Ty -- variable
  | CONST p       -- constant (of type p, i.e. prime field)
  | BOOLEAN Bool

    -- Arithmetic operations
  | ADD (DSL p) (DSL p) -- addition
  | SUB (DSL p) (DSL p) -- subtraction
  | MUL (DSL p) (DSL p) -- multiplication
  | DIV (DSL p) (DSL p) -- division

  | ADDC (DSL p) p -- addition with a constant
  | MULC (DSL p) p -- multiplication with a constant
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

  | BoolToF (DSL p)
  deriving (Show, Eq, Ord)

infixr 5 `CONS`


{-@ measure vlength @-}
{-@ vlength :: DSL p -> Nat @-}
vlength :: DSL p -> Int
vlength (VAR _ (TVec _ n)) = n
vlength (NIL _)     = 0
vlength (CONS _ ps) = 1 + vlength ps
vlength _           = 1

{-@ measure isVar @-}
isVar :: DSL p -> Bool
isVar (VAR {}) = True
isVar _        = False


{-@ boolFromIntegral :: a -> {v:DSL p | typed v TBool} @-}
boolFromIntegral :: Integral a => a -> DSL p
boolFromIntegral x = BOOLEAN (x /= 0)


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

{-@ reflect sameType @-}
sameType :: DSL p -> DSL p -> Bool
sameType program1 program2 = inferType program1 == inferType program2

{-@ reflect scalar @-}
scalar :: DSL p -> Bool
scalar p = case inferType p of
  Nothing       -> False
  Just TVec {}  -> False
  Just _        -> True


{-@ reflect vector @-}
vector :: DSL p -> Bool
vector p = case inferType p of
  Nothing      -> False
  Just TVec {} -> True
  Just _       -> False


{-@ reflect inferType @-}
inferType :: DSL p -> Maybe Ty
inferType (VAR _ τ) = Just τ
inferType (CONST _) = Just TF
inferType (BOOLEAN _) = Just TBool

inferType (ADD p1 p2) | inferType p1 == Just TF && inferType p2 == Just TF
                      = Just TF
inferType (SUB p1 p2) | inferType p1 == Just TF && inferType p2 == Just TF
                      = Just TF
inferType (MUL p1 p2) | inferType p1 == Just TF && inferType p2 == Just TF
                      = Just TF
inferType (DIV p1 p2) | inferType p1 == Just TF && inferType p2 == Just TF
                      = Just TF

inferType (ADDC p1 _) | inferType p1 == Just TF = Just TF
inferType (MULC p1 _) | inferType p1 == Just TF = Just TF
inferType (LINCOMB _ p1 _ p2) | inferType p1 == Just TF && inferType p2 == Just TF
                              = Just TF

inferType (NOT p1)    | inferType p1 == Just TBool = Just TBool
inferType (AND p1 p2) | inferType p1 == Just TBool && inferType p2 == Just TBool
                      = Just TBool
inferType (OR  p1 p2) | inferType p1 == Just TBool && inferType p2 == Just TBool
                      = Just TBool
inferType (XOR p1 p2) | inferType p1 == Just TBool && inferType p2 == Just TBool
                      = Just TBool

inferType (UnsafeNOT p1)    | inferType p1 == Just TBool = Just TBool
inferType (UnsafeAND p1 p2) | inferType p1 == Just TBool && inferType p2 == Just TBool
                            = Just TBool
inferType (UnsafeOR  p1 p2) | inferType p1 == Just TBool && inferType p2 == Just TBool
                            = Just TBool
inferType (UnsafeXOR p1 p2) | inferType p1 == Just TBool && inferType p2 == Just TBool
                            = Just TBool

inferType (EQL p1 p2) | inferType p1 == Just TF && inferType p2 == Just TF
                      = Just TBool
inferType (ISZERO p1) | inferType p1 == Just TF = Just TBool
inferType (EQLC p1 _) | inferType p1 == Just TF = Just TBool

inferType (NIL τ) = Just (TVec τ 0)
inferType (CONS h ts) | Just τ  <- inferType h
                      , Just (TVec τ n) <- inferType ts
                      = Just (TVec τ (n+1))

inferType (BoolToF p) | Just TBool <- inferType p = Just TF

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


-- Labeled DSL
data LDSL p i =
  LWIRE                          i |
  LVAR   String Ty               i |
  LCONST p                       i |

  LADD   (LDSL p i) (LDSL p i)   i |
  LSUB   (LDSL p i) (LDSL p i)   i |
  LMUL   (LDSL p i) (LDSL p i)   i |
  LDIV   (LDSL p i) (LDSL p i) i i |

  LADDC  (LDSL p i) p            i |
  LMULC  (LDSL p i) p            i |
  LLINCOMB p (LDSL p i) p (LDSL p i) i |

  LNOT   (LDSL p i)            i |
  LAND   (LDSL p i) (LDSL p i) i |
  LOR    (LDSL p i) (LDSL p i) i |
  LXOR   (LDSL p i) (LDSL p i) i |

  LUnsafeNOT   (LDSL p i)            i |
  LUnsafeAND   (LDSL p i) (LDSL p i) i |
  LUnsafeOR    (LDSL p i) (LDSL p i) i |
  LUnsafeXOR   (LDSL p i) (LDSL p i) i |

  LEQLC   (LDSL p i) p       i i |

  LNZERO  (LDSL p i)           i |
  LBOOL   (LDSL p i)             |
  LEQA    (LDSL p i) (LDSL p i)
  deriving Show

{-@
data LDSL p i =
  LWIRE                          i |
  LVAR   String     ScalarTy     i |
  LCONST p                       i |

  LADD   (LDSL p i) (LDSL p i)   i |
  LSUB   (LDSL p i) (LDSL p i)   i |
  LMUL   (LDSL p i) (LDSL p i)   i |
  LDIV   (LDSL p i) (LDSL p i) i i |

  LADDC  (LDSL p i) p            i |
  LMULC  (LDSL p i) p            i |

  LLINCOMB p (LDSL p i) p (LDSL p i) i |

  LNOT   (LDSL p i)            i |
  LAND   (LDSL p i) (LDSL p i) i |
  LOR    (LDSL p i) (LDSL p i) i |
  LXOR   (LDSL p i) (LDSL p i) i |

  LUnsafeNOT   (LDSL p i)            i |
  LUnsafeAND   (LDSL p i) (LDSL p i) i |
  LUnsafeOR    (LDSL p i) (LDSL p i) i |
  LUnsafeXOR   (LDSL p i) (LDSL p i) i |

  LEQLC   (LDSL p i) p       i i |

  LNZERO  (LDSL p i)           i |
  LBOOL   (LDSL p i)             |
  LEQA    (LDSL p i) (LDSL p i)
@-}


type Store p = [Assertion p]

-- TODO: this could probably be avoided by using record syntax
{-@ measure outputWire @-}
outputWire :: LDSL p i -> i
outputWire (LWIRE i)      = i

outputWire (LVAR _ _ i)   = i
outputWire (LCONST _ i)   = i
outputWire (LADD _ _ i)   = i
outputWire (LSUB _ _ i)   = i
outputWire (LMUL _ _ i)   = i
outputWire (LDIV _ _ _ i) = i

outputWire (LADDC _ _ i)   = i
outputWire (LMULC _ _ i)   = i
outputWire (LLINCOMB _ _ _ _ i) = i

outputWire (LNOT _   i) = i
outputWire (LAND _ _ i) = i
outputWire (LOR  _ _ i) = i
outputWire (LXOR _ _ i) = i

outputWire (LUnsafeNOT _   i) = i
outputWire (LUnsafeAND _ _ i) = i
outputWire (LUnsafeOR  _ _ i) = i
outputWire (LUnsafeXOR _ _ i) = i

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

nGates (LVAR _ τ _)     = case τ of TF -> 0; TBool -> 1
nGates (LCONST _ _)     = 1
nGates (LADD p1 p2 _)   = 1 + nGates p1 + nGates p2
nGates (LSUB p1 p2 _)   = 1 + nGates p1 + nGates p2
nGates (LMUL p1 p2 _)   = 1 + nGates p1 + nGates p2
nGates (LDIV p1 p2 _ _) = 2 + nGates p1 + nGates p2

nGates (LADDC p1 _ _) = 1 + nGates p1
nGates (LMULC p1 _ _) = 1 + nGates p1
nGates (LLINCOMB _ p1 _ p2 _) = 1 + nGates p1 + nGates p2

nGates (LNOT p1    _) = 2 + nGates p1
nGates (LAND p1 p2 _) = 3 + nGates p1 + nGates p2
nGates (LOR  p1 p2 _) = 3 + nGates p1 + nGates p2
nGates (LXOR p1 p2 _) = 3 + nGates p1 + nGates p2

nGates (LUnsafeNOT p1    _) = 1 + nGates p1
nGates (LUnsafeAND p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LUnsafeOR  p1 p2 _) = 1 + nGates p1 + nGates p2
nGates (LUnsafeXOR p1 p2 _) = 1 + nGates p1 + nGates p2

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
compile m (LVAR _ τ i)   = case τ of
  TF       -> emptyCircuit m
  TBool    -> boolGate m i
  TVec τ n -> error "Vector variables have been unfolded by now"
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
compile m (LADDC p1 k i) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (addGateConst m k [i1, i]) c1
compile m (LMULC p1 k i) = c
  where
    c1 = compile m p1
    i1 = outputWire p1
    c = append' (mulGateConst m k [i1, i]) c1
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
semanticsAreCorrect _ (LVAR _ τ i)   input = case τ of
  TF    -> True              -- field-typed variables don't have restrictions
  TBool -> boolean (input!i) -- bool-typed variables must be boolean
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
semanticsAreCorrect m (LADDC p1 k i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 && input!i == input!i1 + k
semanticsAreCorrect m (LMULC p1 k i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  i1 = outputWire p1
  correct = correct1 && input!i == input!i1 * k
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
vars n name = map' (\i -> name ++ "_" ++ show i) (firstNats n)
