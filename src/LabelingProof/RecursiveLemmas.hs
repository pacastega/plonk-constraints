{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module LabelingProof.RecursiveLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import TypeAliases
import DSL
import Utils
import WitnessGeneration
import Label

import WitnessGenProof.WitnessGenLemmas

import Language.Haskell.Liquid.ProofCombinators

-- well-typedness is propagated to the arguments [DSL] -------------------------

{-@ wellTypedUn :: e1:DSL p -> op:{UnOp p | wellTyped (UN op e1)}
                -> { wellTyped e1 } @-}
wellTypedUn :: DSL p -> UnOp p -> Proof
wellTypedUn e1 op = trivial


{-@ wellTypedBin :: e1:DSL p -> e2:DSL p
                 -> op:{BinOp p | wellTyped (BIN op e1 e2)}
                 -> { wellTyped e1 && wellTyped e2 } @-}
wellTypedBin :: DSL p -> DSL p -> BinOp p -> Proof
wellTypedBin e1 e2 op = trivial


{-@ wellTypedCons :: e1:DSL p -> e2:{DSL p | wellTyped (CONS e1 e2)}
                  -> { wellTyped e1 && wellTyped e2 } @-}
wellTypedCons :: DSL p -> DSL p -> Proof
wellTypedCons e1 e2 = trivial


-- subexpressions are smaller [DSL] --------------------------------------------

{-@ sizeUn :: e1:DSL p -> op:UnOp p -> { size e1 < size (UN op e1) } @-}
sizeUn :: DSL p -> UnOp p -> Proof
sizeUn e1 op = trivial


{-@ sizeBin :: e1:DSL p -> e2:DSL p -> op:BinOp p
            -> { size e1 < size (BIN op e1 e2) &&
                 size e2 < size (BIN op e1 e2) } @-}
sizeBin :: DSL p -> DSL p -> BinOp p -> Proof
sizeBin e1 e2 op = trivial


{-@ sizeCons :: e1:DSL p -> e2:DSL p
             -> { size e1 < size (CONS e1 e2) &&
                  size e2 < size (CONS e1 e2) } @-}
sizeCons :: DSL p -> DSL p -> Proof
sizeCons e1 e2 = trivial


-- well-typedness and well-formedness are propagated to the arguments [LDSL] ---

-- if ↑e1 is well-typed and well-formed, then so is e1
{-@ wfCast :: e1:{LDSL p Int | wfE (LBoolToF e1) && wellTyped' (LBoolToF e1)}
           -> { wfE e1 && wellTyped' e1 } @-}
wfCast :: (Num p) => LDSL p Int -> Proof
wfCast e1 = trivial


-- if e1/e2 is well-typed and well-formed, then so are e1 and e2
{-@ wfDiv :: e1:LDSL p Int -> e2:LDSL p Int -> w:Int
          -> i:{Int | wfE (LDIV e1 e2 w i) && wellTyped' (LDIV e1 e2 w i)}
          -> { wfE e1 && wfE e2 && wellTyped' e1 && wellTyped' e2 } @-}
wfDiv :: LDSL p Int -> LDSL p Int -> Int -> Int -> Proof
wfDiv e1 e2 w i = trivial


-- if e1==e2 is well-typed and well-formed, then so are e1 and e2
{-@ wfEql :: e1:LDSL p Int -> e2:LDSL p Int -> d:Int -> w:Int
          -> i:{Int | wfE        (LEQLC (LBIN SUB e1 e2 d) 0 w i)
                   && wellTyped' (LEQLC (LBIN SUB e1 e2 d) 0 w i)}
          -> { wfE e1 && wfE e2 && wellTyped' e1 && wellTyped' e2 } @-}
wfEql :: (Num p) => LDSL p Int -> LDSL p Int -> Int -> Int -> Int -> Proof
wfEql e1 e2 d w i = trivial


-- if e1==k is well-typed and well-formed, then so is e1
{-@ wfIsk :: e1:LDSL p Int -> k:p -> w:Int
          -> i:{Int | wfE (LEQLC e1 k w i) && wellTyped' (LEQLC e1 k w i)}
          -> { wfE e1 && wellTyped' e1 } @-}
wfIsk :: (Num p) => LDSL p Int -> p -> Int -> Int -> Proof
wfIsk e1 k w i = trivial


-- if □e1 is well-typed and well-formed, then so is e1
{-@ wfUn :: e1:LDSL p Int -> op:UnOp' p
         -> i:{Int | wfE (LUN op e1 i) && wellTyped' (LUN op e1 i)}
         -> { wfE e1 && wellTyped' e1 } @-}
wfUn :: (Num p) => LDSL p Int -> UnOp p -> Int -> Proof
wfUn e1 op i = trivial


-- if e1⮾e2 is well-typed and well-formed, then so are e1 and e2
{-@ wfBin :: e1:LDSL p Int -> e2:LDSL p Int -> op:BinOp' p
          -> i:{Int | wfE (LBIN op e1 e2 i) && wellTyped' (LBIN op e1 e2 i)}
          -> { wfE e1 && wfE e2 && wellTyped' e1 && wellTyped' e2 } @-}
wfBin :: LDSL p Int -> LDSL p Int -> BinOp p -> Int -> Proof
wfBin e1 e2 op i = trivial


-- if e1::e2 is well-typed and well-formed, then so are e1 and e2 --------------
{-@ wfCons :: e1:LDSL p Int
           -> e2:{LDSL p Int | wfE (LCONS e1 e2) && wellTyped' (LCONS e1 e2)}
           -> { wfE e1 && wfE e2 && wellTyped' e1 && wellTyped' e2 } @-}
wfCons :: LDSL p Int -> LDSL p Int -> Proof
wfCons e1 e2 = trivial


-- freshness is propagated to the arguments ------------------------------------

-- if fresh(e1/e2, σ), then also fresh(e1,σ) and fresh(e2,σ1)
{-@ freshDiv1 :: m:Nat
              -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
              -> w:Btwn 0 m -> i:Btwn 0 m
              -> σ:{WireValuation p m | freshE (LDIV e1 e2 w i) σ}
              -> { freshE e1 σ } @-}
freshDiv1 :: (Ord p, Fractional p) => Int
          -> LDSL p Int -> LDSL p Int -> Int -> Int
          -> WireValuation p
          -> Proof
freshDiv1 m e1 e2 w i σ = trivial

{-@ freshDiv2 :: m:Nat -> ρ:NameValuation p
              -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
              -> w:Btwn 0 m -> i:{Btwn 0 m | wellTyped' (LDIV e1 e2 w i)
                                            && wfE (LDIV e1 e2 w i)}
              -> σ:{WireValuation p m | freshE (LDIV e1 e2 w i) σ}
              -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}
              -> { freshE e2 σ1 } @-}
freshDiv2 :: (Ord p, Fractional p) => Int -> NameValuation p
          -> LDSL p Int -> LDSL p Int -> Int -> Int
          -> WireValuation p -> WireValuation p
          -> Proof
freshDiv2 m ρ e1 e2 w i σ σ1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- if fresh(↑e1, σ), then also fresh(e1,σ)
{-@ freshCast :: m:Nat
              -> e1:LDSL p (Btwn 0 m)
              -> σ:{WireValuation p m | freshE (LBoolToF e1) σ}
              -> { freshE e1 σ } @-}
freshCast :: (Ord p, Fractional p)
          => Int -> LDSL p Int -> WireValuation p -> Proof
freshCast m e1 σ = trivial


-- if fresh(e1==e2, σ), then also fresh(e1,σ) and fresh(e2,σ1)
{-@ freshEql1 :: m:Nat
              -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
              -> d:Btwn 0 m -> w:Btwn 0 m -> i:Btwn 0 m
              -> σ:{WireValuation p m | freshE (LEQLC (LBIN SUB e1 e2 d) 0 w i) σ}
              -> { freshE e1 σ } @-}
freshEql1 :: (Ord p, Fractional p) => Int
          -> LDSL p Int -> LDSL p Int -> Int -> Int -> Int
          -> WireValuation p
          -> Proof
freshEql1 m e1 e2 d w i σ = trivial

{-@ freshEql2 :: m:Nat -> ρ:NameValuation p
              -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
              -> d:Btwn 0 m -> w:Btwn 0 m
              -> i:{Btwn 0 m | wellTyped' (LEQLC (LBIN SUB e1 e2 d) 0 w i)
                              && wfE (LEQLC (LBIN SUB e1 e2 d) 0 w i)}
              -> σ:{WireValuation p m | freshE (LEQLC (LBIN SUB e1 e2 d) 0 w i) σ}
              -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}
              -> { freshE e2 σ1 } @-}
freshEql2 :: (Ord p, Fractional p) => Int -> NameValuation p
          -> LDSL p Int -> LDSL p Int -> Int -> Int -> Int
          -> WireValuation p -> WireValuation p
          -> Proof
freshEql2 m ρ e1 e2 d w i σ σ1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- if fresh(e1==0, σ), then also fresh(e1,σ)
{-@ freshIsk :: m:Nat
             -> e1:LDSL p (Btwn 0 m) -> k:p
             -> w:Btwn 0 m -> i:Btwn 0 m
             -> σ:{WireValuation p m | freshE (LEQLC e1 k w i) σ}
             -> { freshE e1 σ } @-}
freshIsk :: (Ord p, Fractional p)
         => Int -> LDSL p Int -> p -> Int -> Int -> WireValuation p -> Proof
freshIsk m e1 k w i σ = trivial


-- if fresh(e1==0, σ), then also fresh(e1,σ)
{-@ freshUn :: m:Nat
            -> e1:LDSL p (Btwn 0 m) -> op:UnOp' p
            -> i:Btwn 0 m
            -> σ:{WireValuation p m | freshE (LUN op e1 i) σ}
            -> { freshE e1 σ } @-}
freshUn :: (Ord p, Fractional p)
        => Int -> LDSL p Int -> UnOp p -> Int -> WireValuation p -> Proof
freshUn m e1 op i σ = trivial


-- if fresh(e1⮾e2, σ), then also fresh(e1,σ) and fresh(e2,σ1)
{-@ freshBin1 :: m:Nat
              -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
              -> op:BinOp' p -> i:Btwn 0 m
              -> σ:{WireValuation p m | freshE (LBIN op e1 e2 i) σ}
              -> { freshE e1 σ } @-}
freshBin1 :: (Ord p, Fractional p) => Int
          -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
          -> WireValuation p
          -> Proof
freshBin1 m e1 e2 op i σ = trivial

{-@ freshBin2 :: m:Nat -> ρ:NameValuation p
              -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
              -> op:BinOp' p -> i:{Btwn 0 m | wellTyped' (LBIN op e1 e2 i)
                                            && wfE (LBIN op e1 e2 i)}
              -> σ:{WireValuation p m | freshE (LBIN op e1 e2 i) σ}
              -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}
              -> { freshE e2 σ1 } @-}
freshBin2 :: (Ord p, Fractional p) => Int -> NameValuation p
          -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
          -> WireValuation p -> WireValuation p
          -> Proof
freshBin2 m ρ e1 e2 op i σ σ1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- if fresh(e1::e2, σ), then also fresh(e1,σ) and fresh(e2,σ1)
{-@ freshCons1 :: m:Nat
               -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
               -> σ:{WireValuation p m | freshE (LCONS e1 e2) σ}
               -> { freshE e1 σ } @-}
freshCons1 :: (Ord p, Fractional p) => Int
           -> LDSL p Int -> LDSL p Int
           -> WireValuation p
           -> Proof
freshCons1 m e1 e2 σ = trivial

{-@ freshCons2 :: m:Nat -> ρ:NameValuation p
               -> e1:LDSL p (Btwn 0 m)
               -> e2:{LDSL p (Btwn 0 m) | wellTyped' (LCONS e1 e2)
                                         && wfE (LCONS e1 e2)}
               -> σ:{WireValuation p m | freshE (LCONS e1 e2) σ}
               -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}
               -> { freshE e2 σ1 } @-}
freshCons2 :: (Ord p, Fractional p) => Int -> NameValuation p
           -> LDSL p Int -> LDSL p Int
           -> WireValuation p -> WireValuation p
           -> Proof
freshCons2 m ρ e1 e2 σ σ1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- if σ ⊢ e and σ' ≥ σ, then also σ' ⊢ e [LDSL] --------------------------------

{-@ coherentEIncr :: m:Nat -> e:TypedLDSL p (Btwn 0 m)
                  -> {σ1:WireValuation p m | closedExpr m σ1 e && coherentE m e σ1}
                  -> σ2:WireValuation p m
                  -> MapGE σ2 σ1
                  -> { coherentE m e σ2 } @-}
coherentEIncr :: (Eq p, Fractional p) => Int -> LDSL p Int -> WireValuation p
              -> WireValuation p -> (Int -> Proof) -> Proof
coherentEIncr m e σ1 σ2 π = case e of
  LWIRE  _ i -> trivial
  LVAR _ τ i -> case τ of
    TF -> trivial
    TBool -> π i
  LCONST _ i -> π i
  LBOOL  _ i -> π i

  LDIV e1 e2  w i -> coherentEIncr m e1 σ1 σ2 π ? coherentEIncr m e2 σ1 σ2 π
                   ? π (outputWire e1) ? π (outputWire e2) ? π i ? π w
  LUN  op e1    i -> coherentEIncr m e1 σ1 σ2 π ? π (outputWire e1) ? π i
  LBIN op e1 e2 i -> coherentEIncr m e1 σ1 σ2 π ? coherentEIncr m e2 σ1 σ2 π
                   ? π (outputWire e1) ? π (outputWire e2) ? π i
  LBoolToF e1 -> coherentEIncr m e1 σ1 σ2 π
  LEQLC e1 k w i -> coherentEIncr m e1 σ1 σ2 π ? π (outputWire e1) ? π i ? π w
  LNIL _ -> trivial
  LCONS e1 e2 -> coherentEIncr m e1 σ1 σ2 π ? coherentEIncr m e2 σ1 σ2 π


-- workarounds to fix "crash: unknown constant"

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
