{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
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
wgOutputMem :: (Fractional p, Eq p) => Int
            -> NameValuation p -> WireValuation p -> LDSL p Int
            -> WireValuation p -> Proof
wgOutputMem m ρ σ e σ' = wgClosed m ρ σ e σ' ? outputWire e


{-@ wgOutputMemDiv :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
                   -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                   -> w:Btwn 0 m -> i:Btwn 0 m
                   -> e:{TypedLDSL p (Btwn 0 m) | e = LDIV e1 e2 w i
                                               && wfE e && freshE e σ}
                   -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
                   -> { M.member i σ' && M.member w σ' } @-}
wgOutputMemDiv :: (Fractional p, Eq p) => Int
               -> NameValuation p -> WireValuation p -> LDSL p Int -> LDSL p Int
               -> Int -> Int -> LDSL p Int
               -> WireValuation p -> Proof
wgOutputMemDiv m ρ σ e1 e2 w i e σ' = wgClosed m ρ σ e σ'


{-@ wgOutputMemIsk :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
                   -> e1:LDSL p (Btwn 0 m) -> k:p
                   -> w:Btwn 0 m -> i:Btwn 0 m
                   -> e:{TypedLDSL p (Btwn 0 m) | e = LEQLC e1 k w i
                                               && wfE e && freshE e σ}
                   -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
                   -> { M.member i σ' && M.member w σ' } @-}
wgOutputMemIsk :: (Fractional p, Eq p) => Int
               -> NameValuation p -> WireValuation p -> LDSL p Int -> p
               -> Int -> Int -> LDSL p Int
               -> WireValuation p -> Proof
wgOutputMemIsk m ρ σ e1 k w i e σ' = wgClosed m ρ σ e σ'


-- if σ' = wg(σ,e), then keys(σ') = keys(σ) ∪ wires(e) -------------------------

{-@ wgKeysSet :: m:Nat -> ρ:NameValuation p -> σ:WireValuation p m
              -> e:{TypedLDSL p (Btwn 0 m) | wfE e && freshE e σ}
              -> σ':{WireValuation p m | Just σ' == witnessGenE' m ρ σ e}
              -> { M.keysSet σ' == S.union (M.keysSet σ) (wiresE e) } @-}
wgKeysSet :: (Eq p, Fractional p) => Int -> NameValuation p -> WireValuation p
          -> LDSL p Int -> WireValuation p -> Proof
wgKeysSet m ρ σ e σ' = case witnessGenE' m ρ σ e of Just _ -> trivial


-- values assigned by WG to output (and witness) wires -------------------------

{-@ wgLemmaUn :: m:Nat
              -> e1:LDSL p (Btwn 0 m)
              -> op:UnOp' p
              -> i:Btwn 0 m
              -> e:{LDSL p (Btwn 0 m) | e = LUN op e1 i && wellTyped' e && wfE e}
              -> ρ:NameValuation p
              -> σ:{WireValuation p m | freshE e σ}

              -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
              -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}

              -> v1:{p | v1 = M.lookup' (outputWire e1) σ1}

              -> { M.lookup' i σ' = valueUnOp op v1 } @-}
wgLemmaUn :: (Fractional p, Eq p, Ord p)
           => Int -> LDSL p Int -> UnOp p -> Int -> LDSL p Int
           -> NameValuation p -> WireValuation p

           -> WireValuation p -> WireValuation p
           -> p

           -> Proof
wgLemmaUn m e1 op i e ρ σ σ' σ1 v1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial

{-@ wgLemmaBin :: m:Nat
               -> e1:LDSL p (Btwn 0 m)
               -> e2:LDSL p (Btwn 0 m)
               -> op:BinOp' p
               -> i:Btwn 0 m
               -> e:{LDSL p (Btwn 0 m) | e = LBIN op e1 e2 i
                                      && wellTyped' e && wfE e}
               -> ρ:NameValuation p
               -> σ:{WireValuation p m | freshE e σ}

               -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ  e}
               -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ  e1}
               -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 e2}

               -> v1:{p | v1 = M.lookup' (outputWire e1) σ1}
               -> v2:{p | v2 = M.lookup' (outputWire e2) σ2}

               -> { M.lookup' i σ' = valueBinOp op v1 v2 } @-}
wgLemmaBin :: (Fractional p, Eq p, Ord p)
           => Int -> LDSL p Int -> LDSL p Int -> BinOp p -> Int -> LDSL p Int
           -> NameValuation p -> WireValuation p

           -> WireValuation p -> WireValuation p -> WireValuation p
           -> p -> p

           -> Proof
wgLemmaBin m e1 e2 op i e ρ σ σ' σ1 σ2 v1 v2 = case witnessGenE' m ρ σ e1 of
  Just _ -> case witnessGenE' m ρ σ1 e2 of
    Just _ -> trivial


{-@ wgLemmaDiv :: m:Nat
               -> e1:LDSL p (Btwn 0 m)
               -> e2:LDSL p (Btwn 0 m)
               -> w:Btwn 0 m -> i:Btwn 0 m
               -> e:{LDSL p (Btwn 0 m) | e = LDIV e1 e2 w i
                                      && wellTyped' e && wfE e}
               -> ρ:NameValuation p
               -> σ:{WireValuation p m | freshE e σ}

               -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ  e}
               -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ  e1}
               -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 e2}

               -> v1:{p | v1 = M.lookup' (outputWire e1) σ1}
               -> v2:{p | v2 = M.lookup' (outputWire e2) σ2}

               -> { v2 /= 0 &&
                    M.lookup' i σ' = v1 / v2 &&
                    M.lookup' w σ' =  1 / v2 } @-}
wgLemmaDiv :: (Fractional p, Eq p, Ord p)
           => Int -> LDSL p Int -> LDSL p Int -> Int -> Int -> LDSL p Int
           -> NameValuation p -> WireValuation p

           -> WireValuation p -> WireValuation p -> WireValuation p
           -> p -> p

           -> Proof
wgLemmaDiv m e1 e2 w i e ρ σ σ' σ1 σ2 v1 v2 = case witnessGenE' m ρ σ e1 of
  Just _ -> case witnessGenE' m ρ σ1 e2 of
    Just _ -> liquidAssert (σ' == M.insert w (1 / v2) (M.insert i (v1 / v2) σ2))


{-@ wgLemmaIsk :: m:Nat
               -> e1:LDSL p (Btwn 0 m) -> k:p
               -> w:Btwn 0 m -> i:Btwn 0 m
               -> e:{LDSL p (Btwn 0 m) | e = LEQLC e1 k w i
                                     && wellTyped' e && wfE e}
               -> ρ:NameValuation p
               -> σ:{WireValuation p m | freshE e σ}

               -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
               -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}

               -> v1:{p | v1 = M.lookup' (outputWire e1) σ1}

               -> { M.lookup' i σ' = valueIsk_i k v1 &&
                    M.lookup' w σ' = valueIsk_w k v1 } @-}
wgLemmaIsk :: (Fractional p, Ord p)
           => Int -> LDSL p Int -> p -> Int -> Int -> LDSL p Int
           -> NameValuation p -> WireValuation p

           -> WireValuation p -> WireValuation p
           -> p

           -> Proof
wgLemmaIsk m e1 k w i e ρ σ σ' σ1 v1 = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial

{-@ reflect valueIsk_i @-}
valueIsk_i :: (Fractional p, Ord p) => p -> p -> p
valueIsk_i k v = if v == k then one else zero

{-@ reflect valueIsk_w @-}
valueIsk_w :: (Fractional p, Ord p) => p -> p -> p
valueIsk_w k v = if v == k then zero else 1/(v-k)


-- WG increasing ---------------------------------------------------------------

-- wg(σ, e1/e2) ≥ wg(wg(σ, e1), e2)
{-@ wgIncrDiv :: m:Nat
              -> e1:LDSL p (Btwn 0 m)
              -> e2:LDSL p (Btwn 0 m)
              -> w:Btwn 0 m -> i:Btwn 0 m
              -> e:{LDSL p (Btwn 0 m) | e = LDIV e1 e2 w i
                                      && wellTyped' e && wfE e}
              -> ρ:NameValuation p
              -> σ:{WireValuation p m | freshE e σ}

              -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ  e}
              -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ  e1}
              -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 e2}

              -> MapGE σ' σ2 @-}
wgIncrDiv :: (Fractional p, Eq p)
          => Int -> LDSL p Int -> LDSL p Int -> Int -> Int -> LDSL p Int
          -> NameValuation p -> WireValuation p

          -> WireValuation p -> WireValuation p -> WireValuation p
          -> (Int -> Proof)
wgIncrDiv m e1 e2 w i e ρ σ σ' σ1 σ2 j = case witnessGenE' m ρ σ e1 of
  Just _ -> case witnessGenE' m ρ σ1 e2 of
    Just _ -> trivial


-- wg(σ, □e1) ≥ wg(σ, e1)
{-@ wgIncrUn :: m:Nat
             -> e1:LDSL p (Btwn 0 m)
             -> op:UnOp' p
             -> i:Btwn 0 m
             -> e:{LDSL p (Btwn 0 m) | e = LUN op e1 i
                                      && wellTyped' e && wfE e}
             -> ρ:NameValuation p
             -> σ:{WireValuation p m | freshE e σ}

             -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
             -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}

             -> MapGE σ' σ1 @-}
wgIncrUn :: (Fractional p, Eq p)
         => Int -> LDSL p Int -> UnOp p -> Int -> LDSL p Int
         -> NameValuation p -> WireValuation p

         -> WireValuation p -> WireValuation p
         -> (Int -> Proof)
wgIncrUn m e1 op i e ρ σ σ' σ1 j = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- wg(σ, e1⮾e2) ≥ wg(wg(σ, e1), e2)
{-@ wgIncrBin :: m:Nat
              -> e1:LDSL p (Btwn 0 m)
              -> e2:LDSL p (Btwn 0 m)
              -> op:BinOp' p
              -> i:Btwn 0 m
              -> e:{LDSL p (Btwn 0 m) | e = LBIN op e1 e2 i
                                      && wellTyped' e && wfE e}
              -> ρ:NameValuation p
              -> σ:{WireValuation p m | freshE e σ}

              -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ  e}
              -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ  e1}
              -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 e2}

              -> MapGE σ' σ2 @-}
wgIncrBin :: (Fractional p, Eq p)
          => Int -> LDSL p Int -> LDSL p Int -> BinOp p -> Int -> LDSL p Int
          -> NameValuation p -> WireValuation p

          -> WireValuation p -> WireValuation p -> WireValuation p
          -> (Int -> Proof)
wgIncrBin m e1 e2 op i e ρ σ σ' σ1 σ2 j = case witnessGenE' m ρ σ e1 of
  Just _ -> case witnessGenE' m ρ σ1 e2 of
    Just _ -> trivial


-- wg(σ, e1==0) ≥ wg(σ, e1)
{-@ wgIncrIsk :: m:Nat
              -> e1:LDSL p (Btwn 0 m) -> k:p
              -> w:Btwn 0 m -> i:Btwn 0 m
              -> e:{LDSL p (Btwn 0 m) | e = LEQLC e1 k w i
                                     && wellTyped' e && wfE e}
              -> ρ:NameValuation p
              -> σ:{WireValuation p m | freshE e σ}

              -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e}
              -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ e1}

              -> j:{Int | M.member j σ1}
              -> { M.member j σ' && M.lookup' j σ1 == M.lookup' j σ' } @-}
-- inlining of the "MapGE" type alias; doesn't seem to work otherwise
wgIncrIsk :: (Fractional p, Eq p)
          => Int -> LDSL p Int -> p -> Int -> Int -> LDSL p Int
          -> NameValuation p -> WireValuation p

          -> WireValuation p -> WireValuation p
          -> (Int -> Proof)
wgIncrIsk m e1 k w i e ρ σ σ' σ1 j = case witnessGenE' m ρ σ e1 of
  Just _ -> trivial


-- wg(σ, e1::e2) ≥ wg(wg(σ, e1), e2)
{-@ wgIncrCons :: m:Nat
               -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
               -> e:{LDSL p (Btwn 0 m) | e = LCONS e1 e2
                                      && wellTyped' e && wfE e}
               -> ρ:NameValuation p
               -> σ:{WireValuation p m | freshE e σ}

               -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ  e}
               -> σ1:{WireValuation p m | Just σ1 = witnessGenE' m ρ σ  e1}
               -> σ2:{WireValuation p m | Just σ2 = witnessGenE' m ρ σ1 e2}

               -> MapGE σ' σ2 @-}
wgIncrCons :: (Fractional p, Eq p)
           => Int -> LDSL p Int -> LDSL p Int -> LDSL p Int
           -> NameValuation p -> WireValuation p

           -> WireValuation p -> WireValuation p -> WireValuation p
           -> (Int -> Proof)
wgIncrCons m e1 e2 e ρ σ σ' σ1 σ2 j = case witnessGenE' m ρ σ e1 of
  Just _ -> case witnessGenE' m ρ σ1 e2 of
    Just _ -> trivial
