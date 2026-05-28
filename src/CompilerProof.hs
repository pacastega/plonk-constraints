{-# LANGUAGE CPP #-}
{-# OPTIONS -Wno-unused-matches -Wno-unused-imports
            -Wno-redundant-constraints #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--fast" @-}

module CompilerProof where

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
import CompilerLemmas

import Language.Haskell.Liquid.ProofCombinators

-- This is Theorem 1 from the paper
{-@ compileProof :: m:Nat
                 -> pr:{LProg p (Btwn 0 m) | isJust (tyEnv' pr M.MTip)
                                          && wfPtr S.empty pr}
                 -> {σ:WireValuation p m | closedProg m σ pr}
                 -> { coherent m pr σ <=>
                      satisfies (nGates pr) m σ (compile m pr) } @-}
compileProof :: (Eq p, Fractional p)
             => Int -> LProg p Int -> WireValuation p -> Proof
compileProof m (LExpr e) σ = case tyEnvE e M.MTip of
  Just γ -> compileProofE m e σ
compileProof m (LAss a) σ = case tyEnvA a M.MTip of
  Just γ -> compileProofA m a M.MTip γ σ


{-@ compileProofE :: m:Nat
                  -> e:{TypedLDSL p (Btwn 0 m) | isJust (tyEnvE e M.MTip) && wfPtrE S.empty e}
                  -> {σ:WireValuation p m | closedExpr m σ e}
                  -> { coherentE m e σ <=>
                        satisfies (nGatesE e) m σ (compileE m e) } @-}
compileProofE :: (Eq p, Fractional p) => Int -> LDSL p Int
              -> WireValuation p -> Proof
compileProofE m e σ = case tyEnvE e M.MTip of
  Just γ -> compileProofE_ m e M.MTip γ σ S.empty (\_ -> ())


{-@ compileProofE_ :: m:Nat
                  -> e:TypedLDSL p (Btwn 0 m)
                  -> γ:TyEnv' (Btwn 0 m)
                  -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnvE e γ}
                  -> {σ:WireValuation p m | closedExpr m σ e}

                  -> ws:{S.Set (Btwn 0 m) | wfPtrE ws e}

                  -> ( j:{Btwn 0 m | S.member j ws
                                  && M.lookup j γ' = Just TBool} ->
                        { boolean (M.lookup' j σ) } )

                  -> { coherentE m e σ <=>
                       satisfies (nGatesE e) m σ (compileE m e) } @-}
compileProofE_ :: (Eq p, Fractional p) => Int -> LDSL p Int
              -> TyEnv' Int -> TyEnv' Int
              -> WireValuation p -> S.Set Int -> (Int -> Proof) -> Proof
compileProofE_ m e γ γ' σ ws π = case e of
  PTR _ i -> trivial
  LVAR s τ i -> case τ of
    TF -> trivial
    TBool -> trivial
  LCONST x i -> trivial
  LBOOL  b i -> trivial
  LDIV e1 e2 w i -> case tyEnvE e1 γ of
    Just γ1 -> case tyEnvE e2 γ1 of
      Just γ2 -> case insertIfCompatible w TF γ2 of
        Just γw -> ih1 ? ih2 ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
          where
            n1 = nGatesE e1; n2 = nGatesE e2

            {-@ ih1 :: { coherentE m e1 σ <=> satisfies n1 m σ (compileE m e1) } @-}
            ih1 = compileProofE_ m e1 γ  γ1 σ ws π1 ? n1

            {-@ ih2 :: { coherentE m e1 σ =>
                        (coherentE m e2 σ <=> satisfies n2 m σ (compileE m e2) ) } @-}
            ih2 = if coherentE m e1 σ
                  then compileProofE_ m e2 γ1 γ2 σ (ws `S.union` wiresE e1) π2
                  else trivial
                  ? n2

            {-@ π1 :: j:{Btwn 0 m | S.member j ws
                                 && M.lookup j γ1 = Just TBool}
                           -> { boolean (M.lookup' j σ) } @-}
            π1 j = elementLemma j TBool γ1   -- j ∈ γ1
                ?? lookupLemma j γ1          -- γ1[j] = TBool
                ?? tyEnvEIncr e2 γ1 γ2 j    -- γ2[j] = γ1[j] since γ2 ≥ γ1
                ?? insertICIncr w TF γ2 γw j -- γw[j] = γ2[j] since γw ≥ γ2
                ?? insertICIncr i TF γw γ' j -- γ'[j] = γ2[j] since γ' ≥ γ2
                ?? lookupLemma j γ'          -- M.lookup j γ' = Just γ'[j]
                ?? π j

            {-@ π2 :: j:{Btwn 0 m | S.member j (S.union ws (wiresE e1))
                                 && M.lookup j γ2 = Just TBool}
                           -> { coherentE m e1 σ => boolean (M.lookup' j σ) } @-}
            π2 j = elementLemma j TBool γ2 -- j ∈ γ2
                ?? lookupLemma j γ2        -- γ2[j] = TBool

                ?? if S.member j ws -- j ∈ ws ∪ wires(e1); which one is it?
                   -- if j ∈ ws
                   then insertICIncr w TF γ2 γw j -- γ2[j] = γw[j] since γw ≥ γ2
                     ?? insertICIncr i TF γw γ' j -- γw[j] = γ'[j] since γ' ≥ γw
                     ?? lookupLemma j γ'          -- M.lookup j γ' = Just γ'[j]
                     ?? π j                       -- σ[j] ∈ {0,1} since j ∈ ws

                   -- if j ∈ wires(e1) (considering wires(e1) ⊆ keys(γ1))
                   else tyEnvEIncr e2 γ1 γ2 j -- γ2[j] = γ1[j] since γ2 ≥ γ1
                     ?? lookupLemma j γ1       -- M.lookup j γ1 = Just γ1[j]
                     ?? booleanProof' m σ e1 γ γ1 j -- σ ⊢ e1 ⇒ σ[j] ∈ {0,1}


  LUN op e1 i -> case tyEnvE e1 γ of
    Just γ1 -> case op of
      ADDC _ -> proof; MULC _ -> proof;
      NOT -> proof
          ?? booleanLemma1 m e1 σ γ γ1 ws π1

      where
        {-@ ih1 :: { coherentE m e1 σ <=> satisfies n1 m σ (compileE m e1) } @-}
        ih1 = compileProofE_ m e1 γ γ1 σ ws π1 ? n1

        proof = ih1
        n1 = nGatesE e1
        τ = case inferType' e of Just t -> t

        {-@ π1 :: j:{Btwn 0 m | S.member j ws
                             && M.lookup j γ1 = Just TBool}
                       -> { boolean (M.lookup' j σ) } @-}
        π1 j = elementLemma j TBool γ1  -- j ∈ γ1
            ?? lookupLemma j γ1         -- γ1[j] = TBool
            ?? insertICIncr i τ γ1 γ' j -- γ'[j] = γ1[j] since γ' ≥ γ1
            ?? lookupLemma j γ'         -- M.lookup j γ' = Just γ'[j]
            ?? π j

  LBIN op e1 e2 i -> case tyEnvE e1 γ of
    Just γ1 -> case tyEnvE e2 γ1 of
      Just γ2 -> case op of
        ADD -> proof; SUB -> proof; MUL -> proof; LINCOMB _ _ -> proof;
        AND -> proof
            ?? booleanLemma1 m e1 σ γ γ1 ws π1
            ?? booleanLemma2 m op e1 e2 i e σ γ γ1 γ2 γ' ws π1 π2
        OR  -> proof
            ?? booleanLemma1 m e1 σ γ γ1 ws π1
            ?? booleanLemma2 m op e1 e2 i e σ γ γ1 γ2 γ' ws π1 π2
        XOR -> proof
            ?? booleanLemma1 m e1 σ γ γ1 ws π1
            ?? booleanLemma2 m op e1 e2 i e σ γ γ1 γ2 γ' ws π1 π2

        where
          {-@ ih1 :: { coherentE m e1 σ <=> satisfies n1 m σ (compileE m e1) } @-}
          ih1 = compileProofE_ m e1 γ  γ1 σ ws π1

          {-@ ih2 :: { coherentE m e1 σ =>
                      (coherentE m e2 σ <=> satisfies n2 m σ (compileE m e2) ) } @-}
          ih2 = if coherentE m e1 σ
                then compileProofE_ m e2 γ1 γ2 σ (ws `S.union` wiresE e1) π2
                else trivial

          proof = ih1 ? ih2 ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
          n1 = nGatesE e1; n2 = nGatesE e2

          τ = case inferType' e of Just t -> t

          {-@ π1 :: j:{Btwn 0 m | S.member j ws
                               && M.lookup j γ1 = Just TBool}
                         -> { boolean (M.lookup' j σ) } @-}
          π1 j = elementLemma j TBool γ1  -- j ∈ γ1
              ?? lookupLemma j γ1         -- γ1[j] = TBool
              ?? tyEnvEIncr e2 γ1 γ2 j   -- γ2[j] = γ1[j] since γ2 ≥ γ1
              ?? insertICIncr i τ γ2 γ' j -- γ'[j] = γ2[j] since γ' ≥ γ2
              ?? lookupLemma j γ'         -- M.lookup j γ' = Just γ'[j]
              ?? π j

          {-@ π2 :: j:{Btwn 0 m | S.member j (S.union ws (wiresE e1))
                               && M.lookup j γ2 = Just TBool}
                         -> { coherentE m e1 σ => boolean (M.lookup' j σ) } @-}
          π2 j = elementLemma j TBool γ2 -- j ∈ γ2
              ?? lookupLemma j γ2        -- γ2[j] = TBool

              ?? if S.member j ws -- j ∈ ws ∪ wires(e1); which one is it?
                 -- if j ∈ ws
                 then insertICIncr i τ γ2 γ' j -- γ2[j] = γ'[j] since γ' ≥ γ2
                   ?? lookupLemma j γ'         -- M.lookup j γ' = Just γ'[j]
                   ?? π j                      -- σ[j] ∈ {0,1} since j ∈ ws

                 -- if j ∈ wires(e1) (considering wires(e1) ⊆ keys(γ1))
                 else tyEnvEIncr e2 γ1 γ2 j -- γ2[j] = γ1[j] since γ2 ≥ γ1
                   ?? lookupLemma j γ1       -- M.lookup j γ1 = Just γ1[j]
                   ?? booleanProof' m σ e1 γ γ1 j -- σ ⊢ e1 ⇒ σ[j] ∈ {0,1}


  LBoolToF e1 -> compileProofE_ m e1 γ γ' σ ws π
  LEQLC e1 k w i -> case tyEnvE e1 γ of
    Just γ1 -> case insertIfCompatible w TF γ1 of
      Just γw -> compileProofE_ m e1 γ γ1 σ ws π1

        where
          {-@ π1 :: j:{Btwn 0 m | S.member j ws
                               && M.lookup j γ1 = Just TBool}
                         -> { boolean (M.lookup' j σ) } @-}
          π1 j = elementLemma j TBool γ1      -- j ∈ γ1
              ?? lookupLemma j γ1             -- γ1[j] = TBool
              ?? insertICIncr w TF    γ1 γw j -- γw[j] = γ1[j] since γw ≥ γ1
              ?? insertICIncr i TBool γw γ' j -- γ'[j] = γw[j] since γ' ≥ γw
              ?? lookupLemma j γ'             -- M.lookup j γ' = Just γ'[j]
              ?? π j

  LNIL _ -> trivial
  LCONS e1 e2 -> case tyEnvE e1 γ of
    Just γ1 -> ih1 ?? ih2
            ?? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
      where
        n1 = nGatesE e1; n2 = nGatesE e2

        {-@ ih1 :: { coherentE m e1 σ <=> satisfies n1 m σ (compileE m e1) } @-}
        ih1 = compileProofE_ m e1 γ  γ1 σ ws π1 ? n1

        {-@ ih2 :: { coherentE m e1 σ =>
                    (coherentE m e2 σ <=> satisfies n2 m σ (compileE m e2) ) } @-}
        ih2 = if coherentE m e1 σ
              then compileProofE_ m e2 γ1 γ' σ (ws `S.union` wiresE e1) π2
              else trivial
              ? n2

        {-@ π1 :: j:{Btwn 0 m | S.member j ws
                             && M.lookup j γ1 = Just TBool}
                       -> { boolean (M.lookup' j σ) } @-}
        π1 j = elementLemma j TBool γ1
            ?? tyEnvEIncr e2 γ1 γ' j
            ?? lookupLemma j γ1 ?? lookupLemma j γ'
            ?? π j

        {-@ π2 :: j:{Btwn 0 m | S.member j (S.union ws (wiresE e1))
                             && M.lookup j γ' = Just TBool}
                       -> { coherentE m e1 σ => boolean (M.lookup' j σ) } @-}
        π2 j = elementLemma j TBool γ' -- j ∈ γ'
            ?? lookupLemma j γ'        -- γ'[j] = TBool

            ?? if S.member j ws -- j ∈ ws ∪ wires(e1); which one is it?
               -- if j ∈ ws
               then π j -- σ[j] ∈ {0,1} since j ∈ ws

               -- if j ∈ wires(e1) (considering wires(e1) ⊆ keys(γ1))
               else tyEnvEIncr e2 γ1 γ' j -- γ'[j] = γ1[j] since γ' ≥ γ1
                 ?? lookupLemma j γ1       -- M.lookup j γ1 = Just γ1[j]
                 ?? booleanProof' m σ e1 γ γ1 j -- σ ⊢ e1 ⇒ σ[j] ∈ {0,1}


{-@ compileProofA :: m:Nat
                  -> a:{LAss p (Btwn 0 m) | wfPtrA S.empty a}
                  -> γ:TyEnv' (Btwn 0 m)
                  -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnvA a γ}
                  -> {σ:WireValuation p m | closedAssertion m σ a}
                  -> { coherentA m a σ <=>
                       satisfies (nGatesA a) m σ (compileA m a) } @-}
compileProofA :: (Eq p, Fractional p)
              => Int -> LAss p Int -> TyEnv' Int -> TyEnv' Int
              -> WireValuation p -> Proof
compileProofA m a γ γ' σ = case a of
  LNZERO e1 w -> case tyEnvE e1 γ of
    Just γ1 -> compileProofE_ m e1 γ γ1 σ S.empty (\_ -> ())
  LBOOLEAN e1 -> compileProofE_ m e1 γ γ' σ S.empty (\_ -> ())

  LEQA e1 e2  -> case tyEnvE e1 γ of
    Just γ1 -> ih1 ? ih2
             ? satisfiesDistr n1 n2 m σ (compileE m e1) (compileE m e2)
      where n1 = nGatesE e1; n2 = nGatesE e2

            {-@ ih1 :: { coherentE m e1 σ <=> satisfies n1 m σ (compileE m e1) } @-}
            ih1 = compileProofE_ m e1 γ γ1 σ S.empty (\_ -> ()) ? n1

            {-@ ih2 :: { coherentE m e1 σ =>
                        (coherentE m e2 σ <=> satisfies n2 m σ (compileE m e2) ) } @-}
            ih2 = if coherentE m e1 σ
                  then compileProofE_ m e2 γ1 γ' σ (wiresE e1) π2
                  else trivial
                  ? n2

            {-@ π2 :: j:{Btwn 0 m | S.member j (wiresE e1) && M.lookup j γ' = Just TBool}
                   -> { coherentE m e1 σ => boolean (M.lookup' j σ) } @-}
            π2 j = tyEnvEIncr e2 γ1 γ' j
                ?? lookupLemma j γ1 ?? lookupLemma j γ'
                ?? booleanProof' m σ e1 γ γ1 j

{-@ satisfiesDistr :: n1:Nat -> n2:Nat -> m:Nat
                   -> σ:WireValuation p m
                   -> pr1:Circuit p n1 m -> pr2:Circuit p n2 m
                   -> { satisfies (n1+n2) m σ (append' pr1 pr2) <=>
                        satisfies n1 m σ pr1 && satisfies n2 m σ pr2 } @-}
satisfiesDistr :: Num p => Int -> Int -> Int ->
                  WireValuation p -> Circuit p -> Circuit p -> Proof
satisfiesDistr _  _  _ σ []      pr2 = trivial
satisfiesDistr n1 n2 m σ (p1:ps) pr2 = satisfiesDistr (n1-1) n2 m σ ps pr2
