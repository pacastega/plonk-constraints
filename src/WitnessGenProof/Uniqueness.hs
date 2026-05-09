{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--ple-with-undecided-guards" @-}
-- {-@ LIQUID "--fast" @-}
module WitnessGenProof.Uniqueness where

import Constraints
import TypeAliases
import DSL
import Semantics
import Label
import WitnessGeneration

import Utils

import BooleanProof

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import MapLemmas
import LabelingProof.LabelingLemmas
import LabelingProof.RecursiveLemmas
import WitnessGenProof.WitnessGenLemmas
import WitnessGenProof.SemanticsLemmas
import WitnessGenProof.UniquenessLemmas

import Language.Haskell.Liquid.ProofCombinators

{-@ evalWireUnique :: m0:Nat -> m':Nat
                   -> e:TypedDSL p
                   -> ρ:NameValuation p
                   -> λ:LabelEnv p (Btwn 0 m0)

                   -> m:{Nat | m0 <= m && m <= m'}
                   -> e':{TypedLDSL p (Btwn 0 m) | wfE e'}
                   -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                   -> {σ:WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
                   -> Agree λ' ρ σ
                   -> v:{DSLValue p | evalWire m' e' σ = v}

                   -> γ:TyEnv' (Btwn 0 m0)
                   -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ e' γ}
                   -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                                   && M.lookup j γ' = Just TBool}
                          -> { boolean (M.lookup' j σ) } )

                   -> { eval e ρ = Just v }
                    / [size e] @-}
evalWireUnique :: (Fractional p, Ord p) => Int -> Int -> DSL p
               -> NameValuation p -> LabelEnv p Int

               -> Int -> LDSL p Int -> LabelEnv p Int
               -> WireValuation p -> (String -> Proof) -> DSLValue p

               -> TyEnv' Int -> TyEnv' Int -> (Int -> Proof)
               -> Proof
evalWireUnique m0 m' e ρ λ m e' λ' σ π v γ γ' h_boolean = case inferType' e' of
  Just τ -> case e of
    VAR s τ -> case M.lookup s λ of  -- Is the variable labeled already?
      Nothing -> case inferType e of -- NO: we get "LVAR s τ i"
        Just (TVec _) -> error "variables are scalars"
        Just _ -> π s ?? evalWireScalar m' e' σ ?? lookupLemma i σ
          where i = M.lookup' s λ'
      Just j -> case τ of            -- YES: we get "LWIRE τ j"
          TF -> proof
          TBool -> proof ?? outputWireBool e' γ γ'
                ?? labelWFWire' e m0 λ m e' λ' -- could be called "labelEnvElems"
                ?? h_boolean j
        where proof = elementLemma s j λ ?? lookupLemma s λ ?? π s ?? lookupLemma j σ

    CONST x -> trivial
    BOOL b  -> trivial

    UN op e1 -> case op of
      BoolToF -> admit ()
      ISZERO -> admit ()
      EQLC k -> admit ()
      _ -> evalWireUnique m0 m' e1 ρ λ  m1 e1' λ1 σ π v1 γ γ1
               (\j -> lookupInsertIC (outputWire e') τ γ1 γ' j ?? h_boolean j)
        ?? evalWireScalar m' e'  σ
        ?? evalWireScalar m' e1' σ
        where (m1,e1',λ1) = label' e1 m0 λ
              v1 = evalWire m' e1' σ
              Just γ1 = tyEnv'_ e1' γ

    BIN op e1 e2 -> case op of
      DIV -> admit ()
      EQL -> admit ()
      _ -> evalWireUnique m0 m' e1 ρ λ  m1 e1' λ1 σ π v1 γ  γ1 h_boolean
         ? evalWireUnique m1 m' e2 ρ λ1 m2 e2' λ2 σ π v2 γ1 γ2 h_boolean
        where (m1,e1',λ1) = label' e1 m0 λ
              (m2,e2',λ2) = label' e2 m1 λ1
              v1 = evalWire m' e1' σ
              v2 = evalWire m' e2' σ
              Just γ1 = tyEnv'_ e1' γ
              Just γ2 = tyEnv'_ e2' γ1

              {-@ π1 :: Agree λ1 ρ σ @-}
              π1 :: String -> Proof
              π1 x = labelIncrEnv e2 m1 λ1 m2 e2' λ' x ?? π x

              {-@ π2 :: Agree λ ρ σ @-}
              π2 :: String -> Proof
              π2 x = π x

              {-@ h_2 :: j:{Btwn 0 m | S.member j (elemsSet λ2)
                                    && M.lookup j γ2 = Just TBool}
                      -> { boolean (M.lookup' j σ) } @-}
              h_2 :: Int -> Proof
              h_2 j = lookupInsertIC (outputWire e') τ γ2 γ' j ?? h_boolean j

              {-@ h_1 :: j:{Btwn 0 m | S.member j (elemsSet λ1)
                                   && M.lookup j γ1 = Just TBool}
                      -> { boolean (M.lookup' j σ) } @-}
              h_1 :: Int -> Proof
              h_1 j = elementLemma j TBool γ1
                   ?? tyEnv'_incr e2' γ1 γ2 j
                   ?? lookupLemma j γ1 ?? lookupLemma j γ2
                   ?? labelWFWire' e2 m1 λ1 m2 e2' λ'
                   ?? h_2 j


    NIL τ -> trivial
    CONS e1 e2 -> evalWireUnique m0 m' e1 ρ λ  m1 e1' λ1 σ π1 v1 γ  γ1 h_1
                ? evalWireUnique m1 m' e2 ρ λ1 m2 e2' λ2 σ π  v2 γ1 γ' h_boolean
      where (m1,e1',λ1) = label' e1 m0 λ
            (m2,e2',λ2) = label' e2 m1 λ1
            v1 = evalWire m' e1' σ
            v2 = evalWire m' e2' σ
            Just γ1 = tyEnv'_ e1' γ

            {-@ π1 :: Agree λ1 ρ σ @-}
            π1 x = labelIncrEnv e2 m1 λ1 m2 e2' λ' x ?? π x

            {-@ h_1 :: j:{Btwn 0 m | S.member j (elemsSet λ1)
                                  && M.lookup j γ1 = Just TBool}
                    -> { boolean (M.lookup' j σ) } @-}
            h_1 j = elementLemma j TBool γ1
                 ?? tyEnv'_incr e2' γ1 γ' j
                 ?? lookupLemma j γ1 ?? lookupLemma j γ'
                 ?? labelWFWire' e2 m1 λ1 m2 e2' λ'
                 ?? h_boolean j

    _ -> admit ()


{-@ assume admit :: () -> { False } @-}
admit :: () -> ()
admit _ = ()


{-@ assume myAssume :: b:Bool -> {b} @-}
myAssume :: Bool -> ()
myAssume _ = ()
