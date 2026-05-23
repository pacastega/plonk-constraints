{-# LANGUAGE CPP #-}
{-# OPTIONS -Wno-unused-matches -Wno-unused-imports
            -Wno-redundant-constraints #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module CompilerLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import MapLemmas

import qualified Data.Set as S

import Constraints
import Circuits
import Utils
import TypeAliases

import ArithmeticGates
import LogicGates

import DSL

import BooleanProof hiding (foo, barOp)

import Language.Haskell.Liquid.ProofCombinators


{-@ booleanLemma1 :: m:Nat
                  -> e1:{LDSL p (Btwn 0 m) | booleanE e1}
                  -> σ:{WireValuation p m | closedExpr m σ e1}

                  -> γ:TyEnv' (Btwn 0 m)
                  -> γ1:{TyEnv' (Btwn 0 m) | Just γ1 = tyEnv'_ e1 γ}

                  -> ws:{S.Set (Btwn 0 m) | wfWire'_ ws e1}

                  -> π1:( j:{Btwn 0 m | S.member j ws
                                     && M.lookup j γ1 = Just TBool}
                            -> { boolean (M.lookup' j σ) } )

                  -> { coherentE m e1 σ =>
                       boolean (M.lookup' (outputWire e1) σ) } @-}
booleanLemma1 :: (Fractional p, Eq p) => Int -> LDSL p Int -> WireValuation p

              -> TyEnv' Int -> TyEnv' Int
              -> S.Set Int
              -> (Int -> Proof)

              -> Proof
booleanLemma1 m e1 σ γ γ1 ws π1 = outputWireBool e1 γ γ1 ??
  if S.member i1 (wiresE e1)
  then booleanProof' m σ e1 γ γ1 i1
  else wfWireLemma ws e1 ?? π1 i1

  where i1 = outputWire e1


{-@ booleanLemma2 :: m:Nat -> op:BinOp' p
                  -> e1:LDSL p (Btwn 0 m)
                  -> e2:LDSL p (Btwn 0 m)
                  -> i:Btwn 0 m
                  -> e:{TypedLDSL p (Btwn 0 m) | e = LBIN op e1 e2 i
                                              && booleanE e}
                  -> σ:{WireValuation p m | closedExpr m σ e}

                  -> γ:TyEnv' (Btwn 0 m)
                  -> γ1:{TyEnv' (Btwn 0 m) | Just γ1 = tyEnv'_ e1 γ}
                  -> γ2:{TyEnv' (Btwn 0 m) | Just γ2 = tyEnv'_ e2 γ1}
                  -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ e  γ}

                  -> ws:{S.Set (Btwn 0 m) | wfWire'_ ws e}

                  -> π1:( j:{Btwn 0 m | S.member j ws
                                     && M.lookup j γ1 = Just TBool}
                            -> { boolean (M.lookup' j σ) } )

                  -> π2:( j:{Btwn 0 m | S.member j (S.union ws (wiresE e1))
                                     && M.lookup j γ2 = Just TBool}
                            -> { coherentE m e1 σ => boolean (M.lookup' j σ) } )

                  -> { coherentE m e1 σ && coherentE m e2 σ =>
                       boolean (M.lookup' (outputWire e2) σ) } @-}
booleanLemma2 :: (Fractional p, Eq p)
              => Int -> BinOp p -> LDSL p Int -> LDSL p Int -> Int -> LDSL p Int
              -> WireValuation p

              -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
              -> S.Set Int

              -> (Int -> Proof) -> (Int -> Proof)

              -> Proof
booleanLemma2 m op e1 e2 i e σ γ γ1 γ2 γ' ws π1 π2 = outputWireBool e2 γ1 γ2 ??
  if S.member i2 (wiresE e2)
  then booleanProof' m σ e2 γ1 γ2 i2
  else wfWireLemma (ws `S.union` wiresE e1) e2
    ?? π2 i2

  where i2 = outputWire e2


{-@ reflect wfWire'_ @-}
wfWire'_ :: (Ord i) => S.Set i -> LDSL p i -> Bool
wfWire'_ ws e = case e of
  PTR _ j -> S.member j ws -- j appears in the accumulated set of wires
  LVAR _ _ _ -> True
  LCONST _ _ -> True
  LBOOL _ _ -> True

  LDIV e1 e2 _ _ -> wfWire'_ ws                       e1
                 && wfWire'_ (ws `S.union` wiresE e1) e2

  LUN _ e1 _ -> wfWire'_ ws e1
  LBIN _ e1 e2 _ -> wfWire'_ ws                       e1
                 && wfWire'_ (ws `S.union` wiresE e1) e2

  LBoolToF e1 -> wfWire'_ ws e1
  LEQLC e1 _ _ _ -> wfWire'_ ws e1

  LNIL _ -> True
  LCONS e1 e2 -> wfWire'_ ws                       e1
              && wfWire'_ (ws `S.union` wiresE e1) e2


{-@ wfWireLemma :: ws:S.Set i
                -> e:{LDSL p i | wfWire'_ ws e}
                -> { S.isSubsetOf (ptrsE e) (S.union (wiresE e) ws) } @-}
wfWireLemma :: (Ord i) => S.Set i -> LDSL p i -> Proof
wfWireLemma ws e = case e of
  PTR _ j -> trivial
  LVAR _ _ _ -> trivial
  LCONST _ _ -> trivial
  LBOOL _ _ -> trivial

  LDIV e1 e2 _ _ -> wfWireLemma ws e1
                 ?? wfWireLemma (ws `S.union` wiresE e1) e2

  LUN _ e1 _ -> wfWireLemma ws e1
  LBIN _ e1 e2 _ -> wfWireLemma ws e1
                 ?? wfWireLemma (ws `S.union` wiresE e1) e2

  LBoolToF e1 -> wfWireLemma ws e1
  LEQLC e1 _ _ _ -> wfWireLemma ws e1

  LNIL _ -> trivial
  LCONS e1 e2 -> wfWireLemma ws e1
              ?? wfWireLemma (ws `S.union` wiresE e1) e2


{-@ wiresCDistr :: n1:Nat -> n2:Nat -> n:{Nat | n = n1+n2} -> m:Nat
                -> c1:Circuit p n1 m -> c2:Circuit p n2 m
                -> { wiresC n m (append' c1 c2) =
                      S.union (wiresC n1 m c1) (wiresC n2 m c2) } @-}
wiresCDistr :: (Num p) => Int -> Int -> Int -> Int
            -> Circuit p -> Circuit p -> Proof
wiresCDistr n1 n2 n m []     c2 = trivial
wiresCDistr n1 n2 n m (g:gs) c2 = wiresCDistr (n1-1) n2 (n-1) m gs c2


{-@ compWiresLemma :: m:Nat -> e:TypedLDSL p (Btwn 0 m)
                -> { S.isSubsetOf (wiresC (nGatesE e) m (compileE m e))
                                  (S.union (wiresE e) (ptrsE e)) } @-}
compWiresLemma :: (Fractional p, Eq p) => Int -> LDSL p Int -> Proof
compWiresLemma m e = case e of
  PTR _ _ -> trivial
  LVAR _ τ _ -> case τ of
    TF -> trivial
    TBool -> trivial
  LCONST _ _ -> trivial
  LBOOL _ _ -> trivial

  LDIV e1 e2 _ _ -> compWiresLemma m e1 ? compWiresLemma m e2
                  ? wiresCDistr n1 n2 (n1+n2) m (compileE m e1) (compileE m e2)
                  ? outputWire e1 ? outputWire e2
    where n1 = nGatesE e1; n2 = nGatesE e2
  LUN op e1 _ -> case op of
    ADDC k -> proof; MULC k -> proof; NOT -> proof
    where proof = compWiresLemma m e1 ? outputWire e1
  LBIN op e1 e2 _ -> case op of
    ADD -> proof; SUB -> proof; MUL -> proof; LINCOMB _ _ -> proof;
    AND -> proof; OR  -> proof; XOR -> proof;

    where proof = compWiresLemma m e1 ? compWiresLemma m e2
                ? wiresCDistr n1 n2 (n1+n2) m (compileE m e1) (compileE m e2)
                ? outputWire e1 ? outputWire e2
          n1 = nGatesE e1; n2 = nGatesE e2

  LBoolToF e1 -> compWiresLemma m e1 ? outputWire e1
  LEQLC e1 _ _ _ -> compWiresLemma m e1 ? outputWire e1

  LNIL _ -> trivial
  LCONS e1 e2 -> compWiresLemma m e1 ? compWiresLemma m e2
               ? wiresCDistr n1 n2 (n1+n2) m (compileE m e1) (compileE m e2)
    where n1 = nGatesE e1; n2 = nGatesE e2

-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
