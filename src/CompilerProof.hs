{-# LANGUAGE CPP #-}
{-# OPTIONS -Wno-unused-matches -Wno-unused-imports
            -Wno-redundant-constraints #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--fast" @-}

module CompilerProof where

--TODO: copy this over to BooleanProof.hs
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

import BooleanProof

import Language.Haskell.Liquid.ProofCombinators

-- This is Theorem 1 from the paper
-- {-@ compileProof :: m:Nat
--                  -> pr:LProg p (Btwn 0 m)
--                  -> {σ:WireValuation p m | closedProg m σ pr}
--                  -> { coherent m pr σ <=>
--                       satisfies (nGates pr) m σ (compile m pr) } @-}
-- compileProof :: (Eq p, Fractional p)
--              => Int -> LProg p Int -> WireValuation p -> Proof
-- compileProof m (LExpr e) σ = compileProofE m e σ
-- compileProof m (LAss a) σ = compileProofA m a σ

{-@ reflect wfWire'_ @-}
wfWire'_ :: (Ord i) => S.Set i -> LDSL p i -> Bool
wfWire'_ ws e = case e of
  LWIRE _ j -> S.member j ws -- j appears in the accumulated set of wires
  LVAR _ _ _ -> True
  LCONST _ _ -> True
  LBOOL _ _ -> True

  LDIV e1 e2 _ _ -> True
                 --    S.isSubsetOf (wWiresE e1) (ws `S.union` wiresE e1)
                 -- && S.isSubsetOf (wWiresE e2) (ws `S.union` wiresE e1 `S.union` wiresE e2)
                 && wfWire'_ (ws)                     e1
                 && wfWire'_ (ws `S.union` wiresE e1) e2

  LUN _ e1 _ -> wfWire'_ (ws) e1
  LBIN _ e1 e2 _ -> wfWire'_ (ws)                     e1
                 && wfWire'_ (ws `S.union` wiresE e1) e2

  LBoolToF e1 -> wfWire'_ (ws) e1
  LEQLC e1 _ _ _ -> wfWire'_ (ws) e1

  LNIL _ -> True
  LCONS e1 e2 -> wfWire'_ (ws)                     e1
              && wfWire'_ (ws `S.union` wiresE e1) e2


{-@ wfWireLemma :: ws:S.Set i
                -> e:{LDSL p i | wfWire'_ ws e}
                -> { S.isSubsetOf (wWiresE e) (S.union (wiresE e) ws) } @-}
wfWireLemma :: (Ord i) => S.Set i -> LDSL p i -> Proof
wfWireLemma ws e = case e of
  LWIRE _ j -> trivial
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


{-@ compileProofE2 :: m:Nat
                  -> e:{TypedLDSL p (Btwn 0 m) | isJust (tyEnv' e) && wfWire'_ S.empty e}
                  -> {σ:WireValuation p m | closedExpr m σ e}
                  -> { coherentE m e σ <=>
                        satisfies (nGatesE e) m σ (compileE m e) } @-}
compileProofE2 :: (Eq p, Fractional p) => Int -> LDSL p Int
              -> WireValuation p -> Proof
compileProofE2 m e σ = case tyEnv' e of
  Just γ -> compileProofE m e M.MTip γ σ S.empty (booleanProof' m σ e M.MTip γ)
  -- Just γ -> compileProofE m e M.MTip γ σ S.empty (\_ -> ())


{-@ compileProofE :: m:Nat
                  -> e:TypedLDSL p (Btwn 0 m)
                  -> γ:TyEnv' (Btwn 0 m)
                  -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ e γ}
                  -> {σ:WireValuation p m | closedExpr m σ e}

                  -> ws:{S.Set (Btwn 0 m) | wfWire'_ ws e}

                  -> ( j:{Btwn 0 m | S.member j (S.union ws (wiresE e))
                                  && M.lookup j γ' = Just TBool} ->
                        { boolean (M.lookup' j σ) } )

                  -> { coherentE m e σ <=>
                       satisfies (nGatesE e) m σ (compileE m e) } @-}
compileProofE :: (Eq p, Fractional p) => Int -> LDSL p Int
              -> TyEnv' Int -> TyEnv' Int
              -> WireValuation p -> S.Set Int -> (Int -> Proof) -> Proof
compileProofE m e γ γ' σ ws π = case e of
  LWIRE _ i -> trivial
  LVAR s τ i -> case τ of
    TF -> trivial
    TBool -> trivial
  LCONST x i -> trivial
  LBOOL  b i -> trivial
  LDIV e1 e2 w i -> undefined
                    -- case tyEnv'_ e1 γ of
  --   Just γ1 -> case tyEnv'_ e2 γ1 of
  --     Just γ2 -> compileProofE m eTotal γ e1 σ π ? compileProofE m eTotal γ e2 σ π
  --              ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
  --              ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
  --              ? closedExpr m σ e2 ?? M.lookup' (outputWire e2) σ
  --   where n1 = nGatesE e1; n2 = nGatesE e2

  LUN op e1 i -> undefined
    --              case op of
    -- ADDC _    -> proof
    -- MULC _    -> proof
    -- NOT       -> undefined
    --           --    π (outputWire e1)
    --           -- ?? liquidAssert (boolean (M.lookup' (outputWire e1) σ))
    --           -- ?? proof
    -- UnsafeNOT ->  undefined -- π (outputWire e1) ?? proof
    -- where proof = compileProofE m eTotal γ e1 σ π
    --             ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ

  LBIN op e1 e2 i -> case tyEnv'_ e1 γ of
    Just γ1 -> case tyEnv'_ e2 γ1 of
      Just γ2 -> case op of
        ADD -> proof; SUB -> proof; MUL -> proof; LINCOMB _ _ -> proof;
        AND ->        undefined;
        UnsafeAND -> outputWireBool e1 γ  γ1
                  -- ?? booleanProof' m σ e1 γ γ1 (outputWire e1) -- v1 ∈ {0,1}
                  ?? wfWireLemma ws e1
                  ?? π1 (outputWire e1) -- v1 ∈ {0,1}

                  ?? outputWireBool e2 γ1 γ2
                  -- ?? booleanProof' m σ e2 γ1 γ2 (outputWire e2) -- v2 ∈ {0,1}
                  ?? wfWireLemma (S.union ws (wiresE e1)) e2
                  ?? π2 (outputWire e2) -- v2 ∈ {0,1}

                  ?? proof;

        OR  ->        undefined -- proof;
        UnsafeOR  ->  undefined -- proof;

        XOR ->        undefined -- proof;
        UnsafeXOR ->  undefined -- proof;

        where proof = compileProofE m e1 γ  γ1 σ ws                       π1
                   ?? compileProofE m e2 γ1 γ2 σ (ws `S.union` wiresE e1) π2
                   ?? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
              n1 = nGatesE e1; n2 = nGatesE e2

              -- ws1 = ws `S.union` wiresE e1

              τ = case inferType' e of Just t -> t

              --TODO: need to remove this
              {-@ π1 :: j:{Btwn 0 m | S.member j (S.union ws (wiresE e1))
                                   && M.lookup j γ1 = Just TBool}
                             -> { boolean (M.lookup' j σ) } @-}
              π1 j = elementLemma j TBool γ1
                  ?? insertICIncr i τ γ2 γ' j -- γ2[j] = γ'[j] since γ' ≥ γ2
                  ?? tyEnv'_incr e2 γ1 γ2 j   -- γ1[j] = γ2[j] since γ2 ≥ γ1
                  ?? lookupLemma j γ1 ?? lookupLemma j γ'
                  ?? π j

              {-@ π2 :: j:{Btwn 0 m | S.member j (S.union (S.union ws (wiresE e1))
                                                          (wiresE e2))
                                   && M.lookup j γ2 = Just TBool}
                             -> { boolean (M.lookup' j σ) } @-}
              π2 j = elementLemma j TBool γ2
                  ?? insertICIncr i τ γ2 γ' j -- γ2[j] = γ'[j] since γ' ≥ γ2
                  ?? lookupLemma j γ2 ?? lookupLemma j γ'
                  ?? π j


  LBoolToF e1 -> compileProofE m e1 γ γ' σ ws π
  LEQLC e1 k w i -> undefined
    --                 case tyEnv'_ e1 γ of
    -- Just γ1 -> case insertIfCompatible undefined
    --                 compileProofE m e γ γ' e1 σ π -- (\j -> tyEnv'_incr e1 γ γ1 j ?? π j)
    --               ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
  LNIL _ -> trivial
  LCONS e1 e2 -> undefined
    --              case tyEnv'_ e1 γ of
    -- Just γ1 -> compileProofE m e1 γ γ1 σ π1 ? compileProofE m e2 γ1 γ' σ π
    --          ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
    --   where n1 = nGatesE e1; n2 = nGatesE e2

    --         {-@ π1 :: j:{Btwn 0 m | M.lookup j γ1 = Just TBool}
    --                        -> { boolean (M.lookup' j σ) } @-}
    --         π1 j = elementLemma j TBool γ1
    --             ?? tyEnv'_incr e2 γ1 γ' j
    --             ?? lookupLemma j γ1 ?? lookupLemma j γ'
    --             ?? π j

-- -- {-@ compileProofA :: m:Nat
-- --                   -> a:LAss p (Btwn 0 m)
-- --                   -> {σ:WireValuation p m | closedAssertion m σ a}
-- --                   -> { coherentA m a σ <=>
-- --                        satisfies (nGatesA a) m σ (compileA m a) } @-}
-- -- compileProofA :: (Eq p, Fractional p)
-- --               => Int -> LAss p Int -> WireValuation p -> Proof
-- -- compileProofA m a σ = case a of
-- --   LNZERO e1 w -> scalar' e1 ?? compileProofE m eTotal e1 σ
-- --                ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
-- --   LBOOLEAN e1 -> scalar' e1 ?? compileProofE m eTotal e1 σ
-- --                ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
-- --   LEQA e1 e2  -> scalar' e1 ?? compileProofE m eTotal e1 σ
-- --                ? scalar' e2 ?? compileProofE m eTotal e2 σ
-- --                ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
-- --                ? closedExpr m σ e1 ?? M.lookup' (outputWire e1) σ
-- --                ? closedExpr m σ e2 ?? M.lookup' (outputWire e2) σ
-- --     where n1 = nGatesE e1; n2 = nGatesE e2

{-@ satisfiesDistr :: n1:Nat -> n2:Nat -> m:Nat
                   -> σ:WireValuation p m
                   -> pr1:Circuit p n1 m -> pr2:Circuit p n2 m
                   -> { satisfies (n1+n2) m σ (append' pr1 pr2) <=>
                        satisfies n1 m σ pr1 && satisfies n2 m σ pr2 } @-}
satisfiesDistr :: Num p => Int -> Int -> Int ->
                  WireValuation p -> Circuit p -> Circuit p -> Proof
satisfiesDistr _  _  _ σ []      pr2 = trivial
satisfiesDistr n1 n2 m σ (p1:ps) pr2 = satisfiesDistr (n1-1) n2 m σ ps pr2
