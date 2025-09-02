{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--save" @-}

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

data UnOp p = ADDC p | MULC p
            | NOT    | UnsafeNOT
            | ISZERO | EQLC p
            | BoolToF
  deriving (Show, Eq, Ord)

data BinOp p = ADD | SUB | MUL | DIV
             | LINCOMB p p -- linear combination
             | AND       | OR       | XOR
             | UnsafeAND | UnsafeOR | UnsafeXOR
             | EQL
  deriving (Show, Eq, Ord)

{-@ measure desugaredUnOp @-}
desugaredUnOp :: UnOp p -> Bool
desugaredUnOp op = case op of
  ISZERO -> False; EQLC _ -> False; BoolToF -> False -- syntactic sugar
  _ -> True -- all others are "real" operators

{-@ measure desugaredBinOp @-}
desugaredBinOp :: BinOp p -> Bool
desugaredBinOp op = case op of
  DIV -> False; EQL -> False -- syntactic sugar
  _ -> True -- all others are "real" operators


data DSL p =
    VAR String Ty -- variable
  | CONST p       -- constant (of type p, i.e. prime field)
  | BOOLEAN Bool

  | UN  (UnOp p)  (DSL p)         -- unary operators
  | BIN (BinOp p) (DSL p) (DSL p) -- binary operators

    -- Vectors
  | NIL Ty
  | CONS (DSL p) (DSL p)

  deriving (Show, Eq, Ord)

infixr 5 `CONS`

{-@ data DSL p where
      VAR :: name:String -> t:ScalarTy -> DSL p
      CONST :: p -> DSL p
      BOOLEAN :: Bool -> DSL p

      UN  :: (UnOp p)  -> DSL p -> DSL p
      BIN :: (BinOp p) -> DSL p -> DSL p -> DSL p

      NIL :: Ty -> DSL p
      CONS :: (DSL p) -> (DSL p) -> DSL p
@-}

{-@ measure vlength @-}
{-@ vlength :: DSL p -> Nat @-}
vlength :: DSL p -> Int
vlength (VAR _ (TVec _ n)) = n
vlength (NIL _)     = 0
vlength (CONS _ ps) = 1 + vlength ps
vlength _           = 1

{-@ measure isVar @-}
isVar :: DSL p -> Bool
isVar VAR {} = True
isVar _      = False


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
  Nothing      -> False
  Just TVec {} -> False
  Just _       -> True


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

inferType (UN op p) = case op of
  ADDC _ -> if inferType p == Just TF then Just TF else Nothing
  MULC _ -> if inferType p == Just TF then Just TF else Nothing

  NOT       -> if inferType p == Just TBool then Just TBool else Nothing
  UnsafeNOT -> if inferType p == Just TBool then Just TBool else Nothing

  ISZERO -> if inferType p == Just TF then Just TBool else Nothing
  EQLC _ -> if inferType p == Just TF then Just TBool else Nothing

  BoolToF -> if inferType p == Just TBool then Just TF else Nothing

inferType (BIN op p1 p2) = case op of
  ADD -> if inferType p1 == Just TF && inferType p2 == Just TF then Just TF else Nothing
  SUB -> if inferType p1 == Just TF && inferType p2 == Just TF then Just TF else Nothing
  MUL -> if inferType p1 == Just TF && inferType p2 == Just TF then Just TF else Nothing
  DIV -> if inferType p1 == Just TF && inferType p2 == Just TF then Just TF else Nothing

  LINCOMB _ _ -> if inferType p1 == Just TF && inferType p2 == Just TF then Just TF else Nothing

  AND -> if inferType p1 == Just TBool && inferType p2 == Just TBool then Just TBool else Nothing
  OR  -> if inferType p1 == Just TBool && inferType p2 == Just TBool then Just TBool else Nothing
  XOR -> if inferType p1 == Just TBool && inferType p2 == Just TBool then Just TBool else Nothing

  UnsafeAND -> if inferType p1 == Just TBool && inferType p2 == Just TBool then Just TBool else Nothing
  UnsafeOR  -> if inferType p1 == Just TBool && inferType p2 == Just TBool then Just TBool else Nothing
  UnsafeXOR -> if inferType p1 == Just TBool && inferType p2 == Just TBool then Just TBool else Nothing

  EQL -> if inferType p1 == Just TF && inferType p2 == Just TF then Just TBool else Nothing

inferType (NIL τ) = Just (TVec τ 0)
inferType (CONS h ts) | Just τ' <- inferType h
                      , Just (TVec τ n) <- inferType ts
                      , τ' == τ
                      , n >= 0
                      = Just (TVec τ (n+1))

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


{-@ type UnOp'  p = {op:UnOp  p | desugaredUnOp op} @-}
{-@ type BinOp' p = {op:BinOp p | desugaredBinOp op} @-}

-- Labeled DSL
data LDSL p i =
  LWIRE         Ty               i |
  LVAR   String Ty               i |
  LCONST p                       i |

  LDIV   (LDSL p i) (LDSL p i) i i |

  LUN  (UnOp p)  (LDSL p i)            i |
  LBIN (BinOp p) (LDSL p i) (LDSL p i) i |

  LEQLC   (LDSL p i) p       i i |

  LNZERO  (LDSL p i)           i |
  LBOOL   (LDSL p i)             |
  LEQA    (LDSL p i) (LDSL p i)
  deriving (Show, Eq)

{-@
data LDSL p i =
  LWIRE             ScalarTy     i |
  LVAR   String     ScalarTy     i |
  LCONST p                       i |

  LDIV   (LDSL p i) (LDSL p i) i i |

  LUN  (UnOp' p)  (LDSL p i)            i |
  LBIN (BinOp' p) (LDSL p i) (LDSL p i) i |

  LEQLC   (LDSL p i) p       i i |

  LNZERO  (LDSL p i)           i |
  LBOOL   (LDSL p i)             |
  LEQA    (LDSL p i) (LDSL p i)
@-}


type Store p = [Assertion p]

-- TODO: this could probably be avoided by using record syntax
{-@ measure outputWire @-}
outputWire :: LDSL p i -> i
outputWire (LWIRE _ i)    = i

outputWire (LVAR _ _ i)   = i
outputWire (LCONST _ i)   = i

outputWire (LDIV _ _ _ i) = i

outputWire (LUN _ _ i)    = i
outputWire (LBIN _ _ _ i) = i

outputWire (LEQLC _ _ _ i) = i

-- assertions
outputWire (LNZERO p w) = outputWire p
outputWire (LBOOL  p)   = outputWire p
outputWire (LEQA p1 p2) = outputWire p2 --FIXME: assertions don't have output


-- the number of gates needed to compile the program into a circuit
{-@ measure nGates @-}
{-@ nGates :: LDSL p i -> Nat @-}
nGates :: LDSL p i -> Int
nGates (LWIRE _ _)      = 0

nGates (LVAR _ τ _)     = case τ of TF -> 0; TBool -> 1
nGates (LCONST _ _)     = 1

nGates (LDIV p1 p2 _ _) = 2 + nGates p1 + nGates p2

nGates (LUN  op p  _)    = nGates p + case op of
  ADDC _ -> 1; MULC _ -> 1; NOT -> 2; UnsafeNOT -> 1
nGates (LBIN op p1 p2 _) = nGates p1 + nGates p2 + case op of
  ADD -> 1; SUB -> 1; MUL -> 1; LINCOMB _ _ -> 1
  AND -> 3; OR  -> 3; XOR -> 3
  UnsafeAND -> 1; UnsafeOR -> 1; UnsafeXOR -> 1

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
compile m (LWIRE _ _)    = emptyCircuit m
compile m (LVAR _ τ i)   = case τ of
  TF       -> emptyCircuit m
  TBool    -> boolGate m i
  TVec τ n -> error "Vector variables have been unfolded by now"
compile m (LCONST x i)   = constGate m x i

compile m (LDIV p1 p2 w i) = append' (divGate m [i1, i2, i, w]) c'
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2

compile m (LUN op p1 i) = case op of
  ADDC k    -> append' (addGateConst  m k [i1, i]) c1
  MULC k    -> append' (mulGateConst  m k [i1, i]) c1
  NOT       -> append' (notGate       m   [i1, i]) c1
  UnsafeNOT -> append' (unsafeNotGate m   [i1, i]) c1
  where
    c1 = compile m p1; i1 = outputWire p1

compile m (LBIN op p1 p2 i) = case op of
  ADD -> append' (addGate m [i1, i2, i]) c'
  SUB -> append' (addGate m [i, i2, i1]) c'
  MUL -> append' (mulGate m [i1, i2, i]) c'

  LINCOMB k1 k2 -> append' (linCombGate m [k1, k2] [i1, i2, i]) c'

  AND -> append' (andGate m [i1, i2, i]) c'
  OR  -> append' (orGate  m [i1, i2, i]) c'
  XOR -> append' (xorGate m [i1, i2, i]) c'

  UnsafeAND -> append' (unsafeAndGate m [i1, i2, i]) c'
  UnsafeOR  -> append' (unsafeOrGate  m [i1, i2, i]) c'
  UnsafeXOR -> append' (unsafeXorGate m [i1, i2, i]) c'
  where
    c1 = compile m p1; c2 = compile m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2

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
semanticsAreCorrect _ (LWIRE _ _)    _     = True
semanticsAreCorrect _ (LVAR _ τ i)   input = case τ of
  TF    -> True              -- field-typed variables don't have restrictions
  TBool -> boolean (input!i) -- bool-typed variables must be boolean
semanticsAreCorrect _ (LCONST x i)   input = input!i == x

semanticsAreCorrect m (LDIV p1 p2 w i) input = correct where
  correct1 = semanticsAreCorrect m p1 input
  correct2 = semanticsAreCorrect m p2 input
  i1 = outputWire p1; i2 = outputWire p2
  correct = correct1 && correct2 && input!w * input!i2 == 1 &&
    if input!i2 /= 0 then input!i == input!i1 / input!i2 else True

semanticsAreCorrect m (LUN op p1 i) input = case op of
  ADDC k -> correct1 && input!i == input!i1 + k
  MULC k -> correct1 && input!i == input!i1 * k
  NOT    -> correct1 && (input!i == if input!i1 == 1 then 0 else 1) &&
                          boolean (input!i1)
  UnsafeNOT -> correct1 && (input!i == 1 - input!i1)
  where
    correct1 = semanticsAreCorrect m p1 input; i1 = outputWire p1

semanticsAreCorrect m (LBIN op p1 p2 i) input = case op of
  ADD -> correct1 && correct2 && input!i == input!i1 + input!i2
  SUB -> correct1 && correct2 && input!i == input!i1 - input!i2
  MUL -> correct1 && correct2 && input!i == input!i1 * input!i2
  LINCOMB k1 k2 -> correct1 && correct2 && input!i == k1*input!i1 + k2*input!i2
  AND -> correct1 && correct2 &&
    (input!i == if input!i1 == 0 || input!i2 == 0 then 0 else 1) &&
    boolean (input!i1) && boolean (input!i2)
  OR -> correct1 && correct2 &&
    (input!i == if input!i1 == 1 || input!i2 == 1 then 1 else 0) &&
    boolean (input!i1) && boolean (input!i2)
  XOR -> correct1 && correct2 &&
    (input!i == if input!i1 /= input!i2 then 1 else 0) &&
    boolean (input!i1) && boolean (input!i2)
  UnsafeAND -> correct1 && correct2 &&
    (input!i == input!i1 * input!i2)
  UnsafeOR -> correct1 && correct2 &&
    (input!i == input!i1 + input!i2 - input!i1*input!i2)
  UnsafeXOR -> correct1 && correct2 &&
    (input!i == input!i1 + input!i2 - 2*input!i1*input!i2)
  where
    correct1 = semanticsAreCorrect m p1 input
    correct2 = semanticsAreCorrect m p2 input
    i1 = outputWire p1; i2 = outputWire p2

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
vars n name = map' (\i -> var name ++ "_" ++ show i) (firstNats n)
