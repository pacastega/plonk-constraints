{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.WitnessGenLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import TypeAliases
import Utils
import DSL
import Semantics
import WitnessGeneration
import MapLemmas
import Language.Haskell.Liquid.ProofCombinators


-- the first argument does not affect the result of the function ---------------
{-@ wgLemma :: m:Nat -> m':{Nat | m' >= m}
            -> ρ:NameValuation p -> σ:WireValuation p m
            -> e:{TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ}
            -> { witnessGenE' m ρ σ e == witnessGenE' m' ρ σ e } @-}
wgLemma :: (Eq p, Fractional p) => Int -> Int
        -> NameValuation p -> WireValuation p -> LDSL p Int -> Proof
wgLemma m m' ρ σ e = case e of
  LWIRE {} -> trivial
  LVAR {} -> trivial
  LCONST {} -> trivial
  LBOOL  {} -> trivial

  LDIV e1 e2 _ _ -> wgLemma m m' ρ σ e1 ? case witnessGenE' m ρ σ e1 of
    Nothing -> trivial; Just σ1 -> wgLemma m m' ρ σ1 e2

  LUN _ e1 _ -> wgLemma m m' ρ σ e1
  LBIN _ e1 e2 _ -> wgLemma m m' ρ σ e1 ? case witnessGenE' m ρ σ e1 of
    Nothing -> trivial; Just σ1 -> wgLemma m m' ρ σ1 e2

  LBoolToF e1 -> wgLemma m m' ρ σ e1
  LEQLC e1 _ _ _ -> wgLemma m m' ρ σ e1

  LNIL _ ->  trivial
  LCONS e1 e2 -> wgLemma m m' ρ σ e1 ? case witnessGenE' m ρ σ e1 of
    Nothing -> trivial; Just σ1 -> wgLemma m m' ρ σ1 e2


-- WG always produces values in {0,1} for Bool-typed expressions ---------------

{-@ wgBoolean :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
              -> {e:TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ && booleanE e}
              -> {σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e }
              -> { boolean (M.lookup' (outputWire e) σ') } @-}
wgBoolean :: (Eq p, Fractional p) => Int -> NameValuation p -> WireValuation p
          -> LDSL p Int -> WireValuation p -> Proof
wgBoolean m ρ σ e σ' = case e of
  LWIRE  τ i -> elementLemma i value σ ? lookupLemma i σ
              ? witnessGenE' m ρ σ (LWIRE τ i)
    where value = case M.lookup i σ of Just v -> v
  LVAR _ _ i -> trivial
  LBOOL  {} -> trivial

  LUN _ e1 _ -> wgBoolean m ρ σ e1 σ1
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
  LBIN _ e1 e2 _ -> wgBoolean m ρ σ e1 σ1 ? wgBoolean m ρ σ1 e2 σ2
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s

  LBoolToF e1 -> wgBoolean m ρ σ e1 σ'
  LEQLC e1 k _ i -> if M.lookup' (outputWire e1) σ1 == k
                   then trivial else trivial
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s


-- WG never "updates" old keys, only adds new ones -----------------------------
-- Essentially, "witnessGenE'(σ,e) ≥ σ"
{-@ wgIncr :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
           -> {e:TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ}
           -> {σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
           -> MapGE σ' σ @-}
wgIncr :: (Eq p, Fractional p) => Int -> NameValuation p -> WireValuation p
       -> LDSL p Int -> WireValuation p -> (Int -> Proof)
wgIncr m ρ σ e σ' j = case e of
  LWIRE  τ i -> trivial ? witnessGenE' m ρ σ e
  LVAR s τ i -> case τ of
    TF -> trivial
    TBool -> trivial
  LCONST x i -> trivial
  LBOOL  b i -> trivial
  LDIV e1 e2 w i -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
  LUN op e1 i -> wgIncr m ρ σ  e1 σ1 j
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
  LBIN op e1 e2 i -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s
  LBoolToF e1 -> wgIncr m ρ σ e1 σ' j
  LEQLC e1 k w i -> wgIncr m ρ σ  e1 σ1 j
    where σ1 = case witnessGenE' m ρ σ e1 of Just s -> s
  LNIL _ -> trivial
  LCONS e1 e2 -> wgIncr m ρ σ  e1 σ1 j ? wgIncr m ρ σ1 e2 σ2 j
    where σ1 = case witnessGenE' m ρ σ  e1 of Just s -> s
          σ2 = case witnessGenE' m ρ σ1 e2 of Just s -> s


-- WG produces valuations that bind all wires in the expression ----------------

{-@ wgClosed :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
               -> e':{TypedLDSL p (Btwn 0 m) | wfE e' && freshE e' σ}
               -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}
               -> { closedExpr m σ' e' } @-}
wgClosed :: (Eq p, Fractional p) => Int -> NameValuation p -> WireValuation p
           -> LDSL p Int -> WireValuation p -> Proof
wgClosed m ρ σ e' σ' = case witnessGenE' m ρ σ e' of Just _ -> trivial


-- WG works inductively on the subexpressions ----------------------------------

-- if witnessGen succeeds for ↑e1, it also succeeds for e1
{-@ σ1Cast :: m1:Nat -> m:{Nat | m >= m1}
           -> ρ:NameValuation p -> σ:WireValuation p m1
           -> e1:LDSL p (Btwn 0 m1)
           -> e:{TypedLDSL p (Btwn 0 m) | e = LBoolToF e1
                                      && wfE e && freshE e σ}
           -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
           -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1
                                    && σ1 == σ' } @-}
σ1Cast :: (Eq p, Fractional p) => Int -> Int
       -> NameValuation p -> WireValuation p
       -> LDSL p Int -> LDSL p Int
       -> WireValuation p -> WireValuation p
σ1Cast m1 m ρ σ e1 _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1


-- if witnessGen succeeds for e1/e2, it also succeeds for e1 and e2
{-@ σ1Div :: m1:Nat -> m:{Nat | m >= m1}
          -> ρ:NameValuation p -> σ:WireValuation p m1
          -> e1:LDSL p (Btwn 0 m1) -> e2:LDSL p (Btwn 0 m)
          -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LDIV e1 e2 w i
                                      && wfE e && freshE e σ}
          -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
          -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Div :: (Eq p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> Int -> Int
      -> LDSL p Int -> WireValuation p
      -> WireValuation p
σ1Div m1 m ρ σ e1 _e2 _w _i _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1

{-@ σ2Div :: m2:Nat -> m:{Nat | m >= m2}
          -> ρ:NameValuation p -> σ:WireValuation p m2
          -> e1:LDSL p (Btwn 0 m2) -> e2:LDSL p (Btwn 0 m2)
          -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LDIV e1 e2 w i
                                      && wfE e && freshE e σ}
          -> {σ':WireValuation p m  | Just σ' = witnessGenE' m  ρ σ  e}
          -> {σ1:WireValuation p m2 | Just σ1 = witnessGenE' m  ρ σ  e1}
          -> {σ2:WireValuation p m2 | Just σ2 = witnessGenE' m  ρ σ1 e2} @-}
σ2Div :: (Eq p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> Int -> Int
      -> LDSL p Int -> WireValuation p -> WireValuation p
      -> WireValuation p
σ2Div m2 m ρ σ e1 e2 _w _i _e _σ' _σ1 =
  wgLemma m2 m ρ σ e1 ?? case witnessGenE' m2 ρ σ e1 of
    Just σ1 -> wgLemma m2 m ρ σ1 e2 ?? case witnessGenE' m2 ρ σ1 e2 of
      Just σ2 -> σ2


-- if witnessGen succeeds for e1==e2, it also succeeds for e1 and e2
{-@ σ1Eql :: m1:Nat -> m:{Nat | m >= m1}
          -> ρ:NameValuation p -> σ:WireValuation p m1
          -> e1:LDSL p (Btwn 0 m1) -> e2:LDSL p (Btwn 0 m)
          -> d:Btwn 0 m -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LEQLC (LBIN SUB e1 e2 d) 0 w i
                                      && wfE e && freshE e σ}
          -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
          -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Eql :: (Eq p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> Int -> Int -> Int
      -> LDSL p Int -> WireValuation p
      -> WireValuation p
σ1Eql m1 m ρ σ e1 _e2 _d _w _i _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1

{-@ σ2Eql :: m2:Nat -> m:{Nat | m >= m2}
          -> ρ:NameValuation p -> σ:WireValuation p m2
          -> e1:LDSL p (Btwn 0 m2) -> e2:LDSL p (Btwn 0 m2)
          -> d:Btwn 0 m -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LEQLC (LBIN SUB e1 e2 d) 0 w i
                                      && wfE e && freshE e σ}
          -> {σ':WireValuation p m  | Just σ' = witnessGenE' m  ρ σ  e}
          -> {σ1:WireValuation p m2 | Just σ1 = witnessGenE' m  ρ σ  e1}
          -> {σ2:WireValuation p m2 | Just σ2 = witnessGenE' m  ρ σ1 e2} @-}
σ2Eql :: (Eq p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> Int -> Int -> Int
      -> LDSL p Int -> WireValuation p -> WireValuation p
      -> WireValuation p
σ2Eql m2 m ρ σ e1 e2 _d _w _i _e _σ' _σ1 =
  wgLemma m2 m ρ σ e1 ?? case witnessGenE' m2 ρ σ e1 of
    Just σ1 -> wgLemma m2 m ρ σ1 e2 ?? case witnessGenE' m2 ρ σ1 e2 of
      Just σ2 -> σ2


-- if witnessGen succeeds for e1==0, it also succeeds for e1
{-@ σ1Isk :: m1:Nat -> m:{Nat | m >= m1}
          -> ρ:NameValuation p -> σ:WireValuation p m1
          -> e1:LDSL p (Btwn 0 m1) -> k:p
          -> w:Btwn 0 m -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LEQLC e1 k w i
                                      && wfE e && freshE e σ}
          -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
          -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Isk :: (Eq p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> p -> Int -> Int
      -> LDSL p Int -> WireValuation p
      -> WireValuation p
σ1Isk m1 m ρ σ e1 k _w _i _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1


-- if witnessGen succeeds for □e1, it also succeeds for e1
{-@ σ1Un :: m1:Nat -> m:{Nat | m >= m1}
         -> ρ:NameValuation p -> σ:WireValuation p m1
         -> e1:LDSL p (Btwn 0 m1) -> op:UnOp' p
         -> i:Btwn 0 m
         -> e:{TypedLDSL p (Btwn 0 m) | e = LUN op e1 i && wfE e && freshE e σ}
         -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
         -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Un :: (Eq p, Fractional p) => Int -> Int
     -> NameValuation p -> WireValuation p
     -> LDSL p Int -> UnOp p -> Int
     -> LDSL p Int -> WireValuation p
     -> WireValuation p
σ1Un m1 m ρ σ e1 op _i _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1


-- if witnessGen succeeds for e1⮾e2, it also succeeds for e1 and e2
{-@ σ1Bin :: m1:Nat -> m:{Nat | m >= m1}
          -> ρ:NameValuation p -> σ:WireValuation p m1
          -> e1:LDSL p (Btwn 0 m1) -> e2:LDSL p (Btwn 0 m)
          -> op:BinOp' p -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LBIN op e1 e2 i
                                      && wfE e && freshE e σ}
          -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
          -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Bin :: (Eq p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
      -> LDSL p Int -> WireValuation p
      -> WireValuation p
σ1Bin m1 m ρ σ e1 _e2 _op _i _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1

{-@ σ2Bin :: m2:Nat -> m:{Nat | m >= m2}
          -> ρ:NameValuation p -> σ:WireValuation p m2
          -> e1:LDSL p (Btwn 0 m2) -> e2:LDSL p (Btwn 0 m2)
          -> op:BinOp' p -> i:Btwn 0 m
          -> e:{TypedLDSL p (Btwn 0 m) | e = LBIN op e1 e2 i
                                      && wfE e && freshE e σ}
          -> {σ':WireValuation p m  | Just σ' = witnessGenE' m  ρ σ  e}
          -> {σ1:WireValuation p m2 | Just σ1 = witnessGenE' m  ρ σ  e1}
          -> {σ2:WireValuation p m2 | Just σ2 = witnessGenE' m  ρ σ1 e2} @-}
σ2Bin :: (Eq p, Fractional p) => Int -> Int
      -> NameValuation p -> WireValuation p
      -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
      -> LDSL p Int -> WireValuation p -> WireValuation p
      -> WireValuation p
σ2Bin m2 m ρ σ e1 e2 _op _i _e _σ' _σ1 =
  wgLemma m2 m ρ σ e1 ?? case witnessGenE' m2 ρ σ e1 of
    Just σ1 -> wgLemma m2 m ρ σ1 e2 ?? case witnessGenE' m2 ρ σ1 e2 of
      Just σ2 -> σ2


-- if witnessGen succeeds for e1::e2, it also succeeds for e1 and e2
{-@ σ1Cons :: m1:Nat -> m:{Nat | m >= m1}
           -> ρ:NameValuation p -> σ:WireValuation p m1
           -> e1:LDSL p (Btwn 0 m1) -> e2:LDSL p (Btwn 0 m)
           -> e:{TypedLDSL p (Btwn 0 m) | e = LCONS e1 e2
                                      && wfE e && freshE e σ}
           -> σ':{WireValuation p m  | Just σ' = witnessGenE' m ρ σ e}
           -> {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ e1} @-}
σ1Cons :: (Eq p, Fractional p) => Int -> Int
       -> NameValuation p -> WireValuation p
       -> LDSL p Int -> LDSL p Int
       -> LDSL p Int -> WireValuation p
       -> WireValuation p
σ1Cons m1 m ρ σ e1 _e2 _e _σ' = wgLemma m1 m ρ σ e1 ??
  case witnessGenE' m1 ρ σ e1 of Just σ1 -> σ1

{-@ σ2Cons :: m2:Nat -> m:{Nat | m >= m2}
           -> ρ:NameValuation p -> σ:WireValuation p m2
           -> e1:LDSL p (Btwn 0 m2) -> e2:LDSL p (Btwn 0 m2)
           -> e:{TypedLDSL p (Btwn 0 m) | e = LCONS e1 e2
                                      && wfE e && freshE e σ}
           -> {σ':WireValuation p m  | Just σ' = witnessGenE' m  ρ σ  e}
           -> {σ1:WireValuation p m2 | Just σ1 = witnessGenE' m  ρ σ  e1}
           -> {σ2:WireValuation p m2 | Just σ2 = witnessGenE' m  ρ σ1 e2} @-}
σ2Cons :: (Eq p, Fractional p) => Int -> Int
       -> NameValuation p -> WireValuation p
       -> LDSL p Int -> LDSL p Int
       -> LDSL p Int -> WireValuation p -> WireValuation p
       -> WireValuation p
σ2Cons m2 m ρ σ e1 e2 _e _σ' _σ1 =
  wgLemma m2 m ρ σ e1 ?? case witnessGenE' m2 ρ σ e1 of
    Just σ1 -> wgLemma m2 m ρ σ1 e2 ?? case witnessGenE' m2 ρ σ1 e2 of
      Just σ2 -> σ2


-- outputWire(e) is always bound in wg(σ,e) ------------------------------------

{-@ wgOutputMem :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
                -> e:{ScalarLDSL p (Btwn 0 m) | wfE e && freshE e σ}
                -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
                -> { M.member (outputWire e) σ' } @-}
wgOutputMem :: (Fractional p, Ord p) => Int
            -> NameValuation p -> WireValuation p -> LDSL p Int
            -> WireValuation p -> Proof
wgOutputMem m ρ σ e σ' = wgClosed m ρ σ e σ' ? outputWire e


-- if σ' = wg(σ,e), then keys(σ') = keys(σ) ∪ wires(e) -------------------------

{-@ wgKeysSet :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
              -> e:{TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ}
              -> σ':{WireValuation p m | Just σ' == witnessGenE' m ρ σ e}
              -> { M.keysSet σ' == S.union (M.keysSet σ) (wiresE e) } @-}
wgKeysSet :: (Eq p, Fractional p) => Int -> NameValuation p -> WireValuation p
          -> LDSL p Int -> WireValuation p -> Proof
wgKeysSet m ρ σ e σ' = case witnessGenE' m ρ σ e of Just _ -> trivial
