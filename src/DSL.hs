{-# LANGUAGE StandaloneDeriving, CPP #-}
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

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

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

type Store p = [Assertion p]

{-@
data Assertion p =
    NZERO   (ScalarDSL p)
  | BOOLEAN (ScalarDSL p)
  | EQA     (ScalarDSL p) (ScalarDSL p)
@-}


{-@ type UnOp'  p = {op:UnOp  p | desugaredUnOp op} @-}
{-@ type BinOp' p = {op:BinOp p | desugaredBinOp op} @-}


type LDSL p i = LDSLI p i i 

-- Labeled DSL
data LDSLI p i j =
    LWIRE      Ty j
  | LVAR   Var Ty i
  | LCONST p      i

  | LDIV (LDSLI p i j) (LDSLI p i j) i i

  | LUN  (UnOp p)  (LDSLI p i j)            i
  | LBIN (BinOp p) (LDSLI p i j) (LDSLI p i j) i

  | LEQLC   (LDSLI p i j) p i i
  deriving (Show, Eq)

{-@
data LDSLI p i j =
    LWIRE      ScalarTy j
  | LVAR   Var ScalarTy i
  | LCONST p            i

  | LDIV   (LDSLI p i j) (LDSLI p i j) i i

  | LUN  (UnOp' p)  (LDSLI p i j)            i
  | LBIN (BinOp' p) (LDSLI p i j) (LDSLI p i j) i

  | LEQLC   (LDSLI p i j) p i i
@-}


{-@ measure wiresE @-}
wiresE :: (Ord i) => LDSLI p i j -> S.Set i
wiresE (LWIRE {})    = S.empty
wiresE (LVAR  _ _ i) = S.singleton i
wiresE (LCONST  _ i) = S.singleton i
wiresE (LDIV e1 e2 w i) = wiresE e1 `S.union` wiresE e2 `S.union`
                         S.singleton w `S.union` S.singleton i
wiresE (LUN _ e1 i) = wiresE e1 `S.union` S.singleton i
wiresE (LBIN _ e1 e2 i) = wiresE e1 `S.union` wiresE e2 `S.union` S.singleton i
wiresE (LEQLC e1 _ w i) = wiresE e1 `S.union` S.singleton w `S.union` S.singleton i

{-@ measure wWiresE @-}
wWiresE :: (Ord j) => LDSLI p i j -> S.Set j
wWiresE (LWIRE _ i)      = S.singleton i
wWiresE (LVAR {})        = S.empty
wWiresE (LCONST {})      = S.empty
wWiresE (LDIV e1 e2 _ _) = wWiresE e1 `S.union` wWiresE e2
wWiresE (LUN _ e1 _)     = wWiresE e1
wWiresE (LBIN _ e1 e2 _) = wWiresE e1 `S.union` wWiresE e2
wWiresE (LEQLC e1 _ _ _) = wWiresE e1


--FIXME: a LWIRE on its own isn't well-formed, so that case should be False
-- A labeled expression is well-formed when
-- a. sibling subexpressions don't have wire clashes between themselves
-- b. new wires don't clash with subexpressions
-- c. subexpressions are recursively well-formed
{-@ measure wfE @-}
wfE :: (Ord i, Ord j) => LDSLI p i j -> Bool
wfE (LWIRE  _ _) = True
wfE (LVAR _ _ i) = True
wfE (LCONST _ i) = True
wfE (LDIV e1 e2 w i ) = wfE e1 && wfE e2 && (wiresE e1 `disjoint` wiresE e2)
  && (wiresE e1 `S.union` wiresE e2) `disjoint` (S.singleton w `S.union` S.singleton i)
  && w /= i
wfE (LUN _ e1 i) = wfE e1 && (wiresE e1 `disjoint` S.singleton i)
wfE (LBIN _ e1 e2 i) = wfE e1 && wfE e2 && (wiresE e1 `disjoint` wiresE e2)
  && (wiresE e1 `S.union` wiresE e2) `disjoint` (S.singleton i)
wfE (LEQLC e1 _ w i) = wfE e1
  && (wiresE e1) `disjoint` (S.singleton w `S.union` S.singleton i)
  && w /= i


-- every output wire of a LWIRE also appears as an output wire of a "real" expression
{-@ reflect wfLWireE @-}
wfLWireE :: (Ord i) => LDSL p i -> Bool
wfLWireE e = wWiresE e `S.isSubsetOf` wiresE e


{-@ measure inferType' @-}
{-@ inferType' :: LDSLI p i j -> Maybe Ty @-}
inferType' :: LDSLI p i j -> Maybe Ty
inferType' e = case e of
  LWIRE  τ _ -> Just τ
  LVAR _ τ _ -> Just τ
  LCONST _ _ -> Just TF

  LDIV e1 e2 _ _ -> if inferType' e1 == Just TF && inferType' e2 == Just TF
                    then Just TF else Nothing

  LUN op e1 _ -> case op of
    ADDC _ -> if inferType' e1 == Just TF then Just TF else Nothing
    MULC _ -> if inferType' e1 == Just TF then Just TF else Nothing

    NOT       -> if inferType' e1 == Just TBool then Just TBool else Nothing
    UnsafeNOT -> if inferType' e1 == Just TBool then Just TBool else Nothing

  LBIN op e1 e2 _ -> case op of
    ADD -> if inferType' e1 == Just TF && inferType' e2 == Just TF then Just TF else Nothing
    SUB -> if inferType' e1 == Just TF && inferType' e2 == Just TF then Just TF else Nothing
    MUL -> if inferType' e1 == Just TF && inferType' e2 == Just TF then Just TF else Nothing

    LINCOMB _ _ -> if inferType' e1 == Just TF && inferType' e2 == Just TF then Just TF else Nothing

    AND -> if inferType' e1 == Just TBool && inferType' e2 == Just TBool then Just TBool else Nothing
    OR  -> if inferType' e1 == Just TBool && inferType' e2 == Just TBool then Just TBool else Nothing
    XOR -> if inferType' e1 == Just TBool && inferType' e2 == Just TBool then Just TBool else Nothing

    UnsafeAND -> if inferType' e1 == Just TBool && inferType' e2 == Just TBool then Just TBool else Nothing
    UnsafeOR  -> if inferType' e1 == Just TBool && inferType' e2 == Just TBool then Just TBool else Nothing
    UnsafeXOR -> if inferType' e1 == Just TBool && inferType' e2 == Just TBool then Just TBool else Nothing

  LEQLC e1 _ _ _ -> if inferType' e1 == Just TF then Just TBool else Nothing


{-@ reflect wellTyped' @-}
wellTyped' :: LDSL p i -> Bool
wellTyped' e = case inferType' e of
  Just _ -> True
  Nothing -> False


{-@ reflect booleanE @-}
booleanE :: LDSL p i -> Bool
booleanE e = inferType' e == Just TBool


data LAss p i =
    LNZERO   (LDSL p i) i
  | LBOOLEAN (LDSL p i)
  | LEQA     (LDSL p i) (LDSL p i)
  deriving (Show, Eq)

{-@ measure wiresA @-}
wiresA :: (Ord i) => LAss p i -> S.Set i
wiresA (LNZERO e1 w) = wiresE e1 `S.union` S.singleton w
wiresA (LBOOLEAN e1) = wiresE e1
wiresA (LEQA e1 e2)  = wiresE e1 `S.union` wiresE e2

{-@ measure wWiresA @-}
wWiresA :: (Ord i) => LAss p i -> S.Set i
wWiresA (LNZERO e1 _) = wWiresE e1
wWiresA (LBOOLEAN e1) = wWiresE e1
wWiresA (LEQA e1 e2)  = wWiresE e1 `S.union` wWiresE e2

{-@ measure wfA @-}
wfA :: (Ord i) => LAss p i -> Bool
wfA (LNZERO e1 w) = wfE e1 && (wiresE e1 `disjoint` S.singleton w)
wfA (LBOOLEAN e1) = wfE e1
wfA (LEQA  e1 e2) = wfE e1 && wfE e2 && (wiresE e1 `disjoint` wiresE e2)

data LProg p i = LExpr (LDSL p i) | LAss (LAss p i)

{-@ measure wires @-}
wires :: (Ord i) => LProg p i -> S.Set i
wires (LExpr e) = wiresE e
wires (LAss a) = wiresA a

{-@ measure wWires @-}
wWires :: (Ord i) => LProg p i -> S.Set i
wWires (LExpr e) = wWiresE e
wWires (LAss a) = wWiresA a

{-@ reflect wiress @-}
wiress :: (Ord i) => [LProg p i] -> S.Set i
wiress [] = S.empty
wiress (p:ps) = wires p `S.union` wiress ps

{-@ measure wf @-}
wf :: (Ord i) => LProg p i -> Bool
wf (LExpr e) = wfE e
wf (LAss a) = wfA a

-- A list is well-formed when all expressions are well-formed and there are no pair-wise clashes
{-@ reflect wfs @-}
wfs :: (Ord i) => [LProg p i] -> Bool
wfs [] = True
wfs (p:ps) = wf p && disjoint (wires p) (wiress ps) && wfs ps


-- TODO: this could be avoided by using record syntax
{-@ reflect outputWire @-}
{-@ outputWire :: e:LDSLI p i i
               -> {v:i | S.member v (S.union (wiresE e) (wWiresE e))} @-}
outputWire :: LDSLI p i i -> i
outputWire (LWIRE _ i)    = i

outputWire (LVAR _ _ i)   = i
outputWire (LCONST _ i)   = i

outputWire (LDIV _ _ _ i) = i

outputWire (LUN _ _ i)    = i
outputWire (LBIN _ _ _ i) = i

outputWire (LEQLC _ _ _ i) = i


-- the number of gates needed to compile the program into a circuit
{-@ measure nGatesE @-}
{-@ nGatesE :: LDSLI p i j -> Nat @-}
nGatesE :: LDSLI p i j -> Int
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


{-@ inline closedExpr @-}
{-@ closedExpr :: m:Nat -> σ:WireValuation p m -> e:LDSL p (Btwn 0 m) -> Bool @-}
closedExpr :: Int -> WireValuation p -> LDSL p Int -> Bool
closedExpr m σ e = (wiresE e `S.union` wWiresE e) `S.isSubsetOf` M.keysSet σ


{-@ inline closedAssertion @-}
{-@ closedAssertion :: m:Nat -> WireValuation p m -> a:LAss p (Btwn 0 m) -> Bool @-}
closedAssertion :: Int -> WireValuation p -> LAss p Int -> Bool
closedAssertion m σ a = (wiresA a `S.union` wWiresA a) `S.isSubsetOf` M.keysSet σ


{-@ inline closedProg @-}
{-@ closedProg :: m:Nat -> WireValuation p m -> LProg p (Btwn 0 m) -> Bool @-}
closedProg :: Int -> WireValuation p -> LProg p Int -> Bool
closedProg m σ pr = (wires pr `S.union` wWires pr) `S.isSubsetOf` M.keysSet σ


{-@ reflect coherent @-}
{-@ coherent :: m:Nat -> pr:LProg p (Btwn 0 m)
             -> {σ:WireValuation p m | closedProg m σ pr} -> Bool @-}
coherent :: (Eq p, Fractional p) => Int -> LProg p Int -> WireValuation p -> Bool
coherent m (LExpr e) σ = coherentE m e σ
coherent m (LAss a) σ = coherentA m a σ

{-@ reflect coherentE @-}
{-@ coherentE :: m:Nat -> e:LDSL p (Btwn 0 m)
              -> {σ:WireValuation p m | closedExpr m σ e} -> Bool @-}
coherentE :: (Eq p, Fractional p) => Int -> LDSL p Int -> WireValuation p -> Bool
coherentE m e σ = case e of
  LWIRE _ i -> True
  LVAR _ τ i -> case τ of
    TF -> True          -- field-typed variables don't have restrictions
    TBool -> boolean vi -- bool-typed variables must be boolean
      where vi = M.lookup' i σ
  LCONST x i -> vi == x
    where vi = M.lookup' i σ

  LDIV e1 e2 w i -> coherentE m e1 σ && coherentE m e2 σ
                 && vw * v2 == 1
                 && if v2 /= 0 then vi == v1 / v2 else True
    where vi = M.lookup' i σ
          vw = M.lookup' w σ
          v1 = M.lookup' (outputWire e1) σ
          v2 = M.lookup' (outputWire e2) σ

  LUN op e1 i -> case op of
      ADDC k -> c1 && vi == v1 + k
      MULC k -> c1 && vi == v1 * k
      NOT    -> c1 && (vi == if v1 == 1 then 0 else 1) && boolean v1
      UnsafeNOT -> c1 && (vi == 1 - v1)
    where c1 = coherentE m e1 σ
          vi = M.lookup' i σ
          v1 = M.lookup' (outputWire e1) σ

  LBIN op e1 e2 i -> case op of
      ADD -> c1 && c2 && vi == v1 + v2
      SUB -> c1 && c2 && vi == v1 - v2
      MUL -> c1 && c2 && vi == v1 * v2
      LINCOMB k1 k2 -> c1 && c2 && vi == k1*v1 + k2*v2
      AND -> c1 && c2 && boolean v1 && boolean v2
          && (vi == if v1 == 0 || v2 == 0 then 0 else 1)
      OR  -> c1 && c2 && boolean v1 && boolean v2
          && (vi == if v1 == 1 || v2 == 1 then 1 else 0)
      XOR -> c1 && c2 && boolean v1 && boolean v2
          && (vi == if v1 /= v2 then 1 else 0)
      UnsafeAND -> c1 && c2 && (vi == v1 * v2)
      UnsafeOR  -> c1 && c2 && (vi == v1 + v2 - v1*v2)
      UnsafeXOR -> c1 && c2 && (vi == v1 + v2 - 2*v1*v2)
    where c1 = coherentE m e1 σ
          c2 = coherentE m e2 σ
          vi = M.lookup' i σ
          v1 = M.lookup' (outputWire e1) σ
          v2 = M.lookup' (outputWire e2) σ

  LEQLC e1 k w i -> coherentE m e1 σ && boolean vi
                 && ((v1 - k) * vi == 0)
                 && (if v1 == k then vi == 1 else vi == 0 && vw * (v1 - k) == 1)
    where vi = M.lookup' i σ
          vw = M.lookup' w σ
          v1 = M.lookup' (outputWire e1) σ

{-@ reflect coherentA @-}
{-@ coherentA :: m:Nat -> a:LAss p (Btwn 0 m)
              -> {σ:WireValuation p m | closedAssertion m σ a} -> Bool @-}
coherentA :: (Eq p, Fractional p) => Int -> LAss p Int -> WireValuation p -> Bool
coherentA m a σ = case a of
  LNZERO e1 w -> coherentE m e1 σ && (v1 * vw == 1)
    where vw = M.lookup' w σ
          v1 = M.lookup' (outputWire e1) σ
  LBOOLEAN e1 -> coherentE m e1 σ && boolean v1
    where v1 = M.lookup' (outputWire e1) σ
  LEQA e1 e2 -> coherentE m e1 σ && coherentE m e2 σ && v1 == v2
    where v1 = M.lookup' (outputWire e1) σ
          v2 = M.lookup' (outputWire e2) σ


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
