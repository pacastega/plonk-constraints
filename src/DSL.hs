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

data Ty = TF | TBool | TVec Ty deriving (Eq, Ord, Show)
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

type Var = String

data DSL p =
    VAR Var Ty -- variable
  | CONST p       -- constant (of type p, i.e. prime field)
  | BOOL Bool

  | UN  (UnOp p)  (DSL p)         -- unary operators
  | BIN (BinOp p) (DSL p) (DSL p) -- binary operators

    -- Vectors
  | NIL Ty
  | CONS (DSL p) (DSL p)

  deriving (Show, Eq, Ord)

infixr 5 `CONS`

{-@ data DSL p where
      VAR :: name:Var -> ScalarTy -> DSL p
      CONST :: p -> DSL p
      BOOL :: Bool -> DSL p

      UN  :: (UnOp p)  -> DSL p -> DSL p
      BIN :: (BinOp p) -> DSL p -> DSL p -> DSL p

      NIL :: Ty -> DSL p
      CONS :: (DSL p) -> (DSL p) -> DSL p
@-}

{-@ measure vlength @-}
{-@ vlength :: DSL p -> Nat @-}
vlength :: DSL p -> Int
vlength (NIL _)     = 0
vlength (CONS _ ps) = 1 + vlength ps
vlength _           = 1

{-@ measure isVar @-}
isVar :: DSL p -> Bool
isVar VAR {} = True
isVar _      = False


{-@ boolFromIntegral :: a -> BoolDSL p @-}
boolFromIntegral :: Integral a => a -> DSL p
boolFromIntegral x = BOOL (x /= 0)


{-@ reflect typed @-}
typed :: DSL p -> Ty -> Bool
typed p τ = inferType p == Just τ

{-@ type ScalarDSL p = {d:DSL p | scalar d} @-}
{-@ type TypedDSL p = {d:DSL p | wellTyped d} @-}

{-@ type FieldDSL p   = {v:DSL p | typed v TF} @-}
{-@ type BoolDSL  p   = {v:DSL p | typed v TBool} @-}
{-@ type VecDSL   p T = {v:DSL p | typed v (TVec T)} @-}

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
inferType (BOOL  _) = Just TBool

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

inferType (NIL τ) = Just (TVec τ)
inferType (CONS h ts) | Just τ' <- inferType h
                      , Just (TVec τ) <- inferType ts
                      , τ' == τ
                      = Just (TVec τ)

inferType _ = Nothing


-- (Non-expression) assertions
data Assertion p =
    NZERO   (DSL p)            -- non-zero assertion
  | BOOLEAN (DSL p)            -- booleanity assertion
  | EQA     (DSL p) (DSL p)    -- equality assertion
  deriving Show

{-@
data Assertion p =
    NZERO   (ScalarDSL p)
  | BOOLEAN (ScalarDSL p)
  | EQA     (ScalarDSL p) (ScalarDSL p)
@-}


{-@ type UnOp'  p = {op:UnOp  p | desugaredUnOp op} @-}
{-@ type BinOp' p = {op:BinOp p | desugaredBinOp op} @-}

-- Labeled DSL
data LDSL p i =
    LWIRE      Ty i
  | LVAR   Var Ty i
  | LCONST p      i

  | LDIV (LDSL p i) (LDSL p i) i i

  | LUN  (UnOp p)  (LDSL p i)            i
  | LBIN (BinOp p) (LDSL p i) (LDSL p i) i

  | LEQLC   (LDSL p i) p i i
  deriving (Show, Eq)

data LAss p i =
    LNZERO   (LDSL p i) i
  | LBOOLEAN (LDSL p i)
  | LEQA     (LDSL p i) (LDSL p i)
  deriving (Show, Eq)

data LProg p i = LExpr (LDSL p i) | LAss (LAss p i)

{-@
data LDSL p i =
    LWIRE      ScalarTy i
  | LVAR   Var ScalarTy i
  | LCONST p            i

  | LDIV   (LDSL p i) (LDSL p i) i i

  | LUN  (UnOp' p)  (LDSL p i)            i
  | LBIN (BinOp' p) (LDSL p i) (LDSL p i) i

  | LEQLC   (LDSL p i) p i i
@-}


type Store p = [Assertion p]

-- TODO: this could be avoided by using record syntax
{-@ measure outputWire @-}
outputWire :: LDSL p i -> i
outputWire (LWIRE _ i)    = i

outputWire (LVAR _ _ i)   = i
outputWire (LCONST _ i)   = i

outputWire (LDIV _ _ _ i) = i

outputWire (LUN _ _ i)    = i
outputWire (LBIN _ _ _ i) = i

outputWire (LEQLC _ _ _ i) = i


-- the number of gates needed to compile the program into a circuit
{-@ measure nGatesE @-}
{-@ nGatesE :: LDSL p i -> Nat @-}
nGatesE :: LDSL p i -> Int
nGatesE (LWIRE _ _)      = 0

nGatesE (LVAR _ τ _)     = case τ of TF -> 0; TBool -> 1
nGatesE (LCONST _ _)     = 1

nGatesE (LDIV p1 p2 _ _) = 2 + nGatesE p1 + nGatesE p2

nGatesE (LUN  op p  _)    = nGatesE p + case op of
  ADDC _ -> 1; MULC _ -> 1; NOT -> 2; UnsafeNOT -> 1
nGatesE (LBIN op p1 p2 _) = nGatesE p1 + nGatesE p2 + case op of
  ADD -> 1; SUB -> 1; MUL -> 1; LINCOMB _ _ -> 1
  AND -> 3; OR  -> 3; XOR -> 3
  UnsafeAND -> 1; UnsafeOR -> 1; UnsafeXOR -> 1

nGatesE (LEQLC p1 _ _ _) = 2 + nGatesE p1

{-@ measure nGatesA @-}
{-@ nGatesA :: LAss p i -> Nat @-}
nGatesA :: LAss p i -> Int
nGatesA (LNZERO p1 _)    = 1 + nGatesE p1
nGatesA (LBOOLEAN p1)    = 1 + nGatesE p1
nGatesA (LEQA p1 p2)     = 1 + nGatesE p1 + nGatesE p2

{-@ measure nGates @-}
{-@ nGates :: LProg -> Nat @-}
nGates :: LProg p i -> Int
nGates (LExpr e) = nGatesE e
nGates (LAss a) = nGatesA a


-- compile the program into a circuit including the output wire index
{-@ reflect compile @-}
{-@ compile :: m:Nat -> pr:LProg p (Btwn 0 m) -> Circuit p (nGates pr) m @-}
compile :: (Fractional p, Eq p) => Int -> LProg p Int -> Circuit p
compile m (LExpr e) = compileE m e
compile m (LAss a) = compileA m a

{-@ reflect compileE @-}
{-@ compileE :: m:Nat -> e:LDSL p (Btwn 0 m) -> Circuit p (nGatesE e) m @-}
compileE :: (Fractional p, Eq p) => Int -> LDSL p Int -> Circuit p
compileE m (LWIRE _ _)    = emptyCircuit m
compileE m (LVAR _ τ i)   = case τ of
  TF     -> emptyCircuit m
  TBool  -> boolGate m i
  TVec τ -> error "Vector variables have been unfolded by now"
compileE m (LCONST x i)   = constGate m x i

compileE m (LDIV p1 p2 w i) = append' (divGate m [i1, i2, i, w]) c'
  where
    c1 = compileE m p1; c2 = compileE m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2

compileE m (LUN op p1 i) = case op of
  ADDC k    -> append' (addGateConst  m k [i1, i]) c1
  MULC k    -> append' (mulGateConst  m k [i1, i]) c1
  NOT       -> append' (notGate       m   [i1, i]) c1
  UnsafeNOT -> append' (unsafeNotGate m   [i1, i]) c1
  where
    c1 = compileE m p1; i1 = outputWire p1

compileE m (LBIN op p1 p2 i) = case op of
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
    c1 = compileE m p1; c2 = compileE m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2

compileE m (LEQLC p1 k w i) = c
  where
    c1 = compileE m p1
    i1 = outputWire p1
    c = append' (isEqlCGate m k [i1, w, i]) c1

{-@ reflect compileA @-}
{-@ compileA :: m:Nat -> a:LAss p (Btwn 0 m) -> Circuit p (nGatesA a) m @-}
compileA :: (Fractional p, Eq p) => Int -> LAss p Int -> Circuit p
compileA m (LNZERO p1 w) = c
  where
    c1 = compileE m p1
    i1 = outputWire p1
    c = append' (nonZeroGate m [i1, w]) c1
compileA m (LBOOLEAN p1) = c
  where
    c1 = compileE m p1
    i1 = outputWire p1
    c = append' (boolGate m i1) c1
compileA m (LEQA p1 p2) = c
  where
    c1 = compileE m p1; c2 = compileE m p2
    i1 = outputWire p1; i2 = outputWire p2
    c' = append' c1 c2
    c = append' (equalGate m [i1, i2]) c'


{-@ reflect coherent @-}
{-@ coherent :: m:Nat -> LProg p (Btwn 0 m) -> VecN p m -> Bool @-}
coherent :: (Eq p, Fractional p) => Int -> LProg p Int -> Vec p -> Bool
coherent m (LExpr e) σ = coherentE m e σ
coherent m (LAss a) σ = coherentA m a σ

{-@ reflect coherentE @-}
{-@ coherentE :: m:Nat -> LDSL p (Btwn 0 m) -> VecN p m -> Bool @-}
coherentE :: (Eq p, Fractional p) => Int -> LDSL p Int -> Vec p -> Bool
coherentE _ (LWIRE _ _)  _ = True
coherentE _ (LVAR _ τ i) σ = case τ of
  TF    -> True          -- field-typed variables don't have restrictions
  TBool -> boolean (σ!i) -- bool-typed variables must be boolean
coherentE _ (LCONST x i) σ = σ!i == x

coherentE m (LDIV p1 p2 w i) σ = c where
  c1 = coherentE m p1 σ
  c2 = coherentE m p2 σ
  i1 = outputWire p1; i2 = outputWire p2
  c = c1 && c2 && σ!w * σ!i2 == 1 &&
    if σ!i2 /= 0 then σ!i == σ!i1 / σ!i2 else True

coherentE m (LUN op p1 i) σ = case op of
  ADDC k -> c1 && σ!i == σ!i1 + k
  MULC k -> c1 && σ!i == σ!i1 * k
  NOT    -> c1 && (σ!i == if σ!i1 == 1 then 0 else 1) &&
                          boolean (σ!i1)
  UnsafeNOT -> c1 && (σ!i == 1 - σ!i1)
  where
    c1 = coherentE m p1 σ; i1 = outputWire p1

coherentE m (LBIN op p1 p2 i) σ = case op of
  ADD -> c1 && c2 && σ!i == σ!i1 + σ!i2
  SUB -> c1 && c2 && σ!i == σ!i1 - σ!i2
  MUL -> c1 && c2 && σ!i == σ!i1 * σ!i2
  LINCOMB k1 k2 -> c1 && c2 && σ!i == k1*σ!i1 + k2*σ!i2
  AND -> c1 && c2 &&
    (σ!i == if σ!i1 == 0 || σ!i2 == 0 then 0 else 1) &&
    boolean (σ!i1) && boolean (σ!i2)
  OR -> c1 && c2 &&
    (σ!i == if σ!i1 == 1 || σ!i2 == 1 then 1 else 0) &&
    boolean (σ!i1) && boolean (σ!i2)
  XOR -> c1 && c2 &&
    (σ!i == if σ!i1 /= σ!i2 then 1 else 0) &&
    boolean (σ!i1) && boolean (σ!i2)
  UnsafeAND -> c1 && c2 &&
    (σ!i == σ!i1 * σ!i2)
  UnsafeOR -> c1 && c2 &&
    (σ!i == σ!i1 + σ!i2 - σ!i1*σ!i2)
  UnsafeXOR -> c1 && c2 &&
    (σ!i == σ!i1 + σ!i2 - 2*σ!i1*σ!i2)
  where
    c1 = coherentE m p1 σ
    c2 = coherentE m p2 σ
    i1 = outputWire p1; i2 = outputWire p2

coherentE m (LEQLC p1 k w i) σ = c where
  c1 = coherentE m p1 σ
  i1 = outputWire p1
  c = c1 && boolean (σ!i) &&
                        ((σ!i1 - k) * σ!i == 0) &&
                        (if σ!i1 == k
                         then σ!i == 1
                         else σ!i == 0 && σ!w * (σ!i1 - k) == 1)

{-@ reflect coherentA @-}
{-@ coherentA :: m:Nat -> LAss p (Btwn 0 m) -> VecN p m -> Bool @-}
coherentA :: (Eq p, Fractional p) => Int -> LAss p Int -> Vec p -> Bool
coherentA m (LNZERO p1 w) σ = c where
  c1 = coherentE m p1 σ
  i1 = outputWire p1
  c = c1 && (σ!i1 * σ!w == 1)
coherentA m (LBOOLEAN p1) σ = c where
  c1 = coherentE m p1 σ
  i1 = outputWire p1
  c = c1 && boolean (σ!i1)
coherentA m (LEQA p1 p2) σ = c where
  c1 = coherentE m p1 σ
  c2 = coherentE m p2 σ
  i1 = outputWire p1; i2 = outputWire p2
  c = c1 && c2 && (σ!i1 == σ!i2)


{-# NOINLINE counter #-}
counter :: IORef Int
counter = unsafePerformIO $ newIORef 0

{-# NOINLINE fresh #-}
fresh :: () -> IO Int
fresh () = (
    do x <- readIORef counter
       writeIORef counter (x+1)
       return x)

var :: Var -> Var
var name = name ++ "_" ++ show (unsafePerformIO $ fresh ())

{-@ vars :: n:Nat -> Var -> ListN Var n @-}
vars :: Int -> Var -> [Var]
vars n name = map' (\i -> name' ++ "_" ++ show i) (firstNats n)
  where name' = var name
