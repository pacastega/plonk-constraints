{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.UniquenessBase where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import Utils
import TypeAliases

import Constraints
import DSL
import Label
import WitnessGeneration
import Semantics

import BooleanProof hiding (foo, barOp)

import MapLemmas
import LabelingProof.RecursiveLemmas hiding (foo, barOp)
import LabelingProof.LabelingLemmas
import WitnessGenProof.WitnessGenLemmas
import WitnessGenProof.SemanticsLemmas

import WitnessGenProof.UniquenessLemmas

import Language.Haskell.Liquid.ProofCombinators

{-@ uniqueVar :: m0:Nat -> m':Nat
              -> s:Var -> τ:ScalarTy
              -> e:{TypedDSL p | e = VAR s τ}
              -> ρ:NameValuation p
              -> λ:LabelEnv p (Btwn 0 m0)

              -> m:{Nat | m0 <= m && m <= m'}
              -> e':{LDSL p (Btwn 0 m) | wfE e'}
              -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

              -> σ:{WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
              -> Agree λ' ρ σ
              -> v:{DSLValue p | evalWire m' e' σ = v}

              -> γ:TyEnv' (Btwn 0 m')
              -> γ':{TyEnv' (Btwn 0 m') | Just γ' = tyEnv'_ e' γ}
              -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                              && M.lookup j γ' = Just TBool}
                     -> { boolean (M.lookup' j σ) } )

              -> { eval e ρ = Just v } @-}
uniqueVar :: (Fractional p, Ord p)
          => Int -> Int -> Var -> Ty -> DSL p
          -> NameValuation p -> LabelEnv p Int

          -> Int -> LDSL p Int -> LabelEnv p Int

          -> WireValuation p -> (String -> Proof)
          -> DSLValue p

          -> TyEnv' Int -> TyEnv' Int
          -> (Int -> Proof)

          -> Proof
uniqueVar m0 m' s τ e ρ λ m e' λ' σ π v γ γ' h_boolean =
  case M.lookup s λ of             -- Is the variable labeled already?
    Nothing -> case inferType e of -- NO: we get "LVAR s τ i"
      Just (TVec _) -> error "variables are scalars"
      Just _ -> π s ?? evalWireScalar m' e' σ ?? lookupLemma i σ
        where i = M.lookup' s λ'
    Just j -> case τ of            -- YES: we get "PTR τ j"
        TF -> proof
        TBool -> proof ?? outputWireBool e' γ γ'
              ?? labelWFWire' e m0 λ m e' λ' -- FIXME: could be called "labelEnvElems"
              ?? h_boolean j
      where proof = elementLemma s j λ
                 ?? lookupLemma s λ ?? π s ?? lookupLemma j σ

{-@ uniqueConst :: m0:Nat -> m':Nat
                -> x:p
                -> e:{TypedDSL p | e = CONST x}
                -> ρ:NameValuation p
                -> λ:LabelEnv p (Btwn 0 m0)

                -> m:{Nat | m0 <= m && m <= m'}
                -> e':{LDSL p (Btwn 0 m) | wfE e'}
                -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                -> σ:{WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
                -> Agree λ' ρ σ
                -> v:{DSLValue p | evalWire m' e' σ = v}

                -> γ:TyEnv' (Btwn 0 m')
                -> γ':{TyEnv' (Btwn 0 m') | Just γ' = tyEnv'_ e' γ}
                -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                                && M.lookup j γ' = Just TBool}
                       -> { boolean (M.lookup' j σ) } )

                -> { eval e ρ = Just v } @-}
uniqueConst :: (Fractional p, Ord p)
            => Int -> Int -> p -> DSL p
            -> NameValuation p -> LabelEnv p Int

            -> Int -> LDSL p Int -> LabelEnv p Int

            -> WireValuation p -> (String -> Proof)
            -> DSLValue p

            -> TyEnv' Int -> TyEnv' Int
            -> (Int -> Proof)

            -> Proof
uniqueConst m0 m' x e ρ λ m e' λ' σ π v γ γ' h_boolean = trivial


{-@ uniqueBool :: m0:Nat -> m':Nat
               -> b:Bool
               -> e:{TypedDSL p | e = BOOL b}
               -> ρ:NameValuation p
               -> λ:LabelEnv p (Btwn 0 m0)

               -> m:{Nat | m0 <= m && m <= m'}
               -> e':{LDSL p (Btwn 0 m) | wfE e'}
               -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

               -> σ:{WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
               -> Agree λ' ρ σ
               -> v:{DSLValue p | evalWire m' e' σ = v}

               -> γ:TyEnv' (Btwn 0 m')
               -> γ':{TyEnv' (Btwn 0 m') | Just γ' = tyEnv'_ e' γ}
               -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                               && M.lookup j γ' = Just TBool}
                      -> { boolean (M.lookup' j σ) } )

               -> { eval e ρ = Just v } @-}
uniqueBool :: (Fractional p, Ord p)
           => Int -> Int -> Bool -> DSL p
           -> NameValuation p -> LabelEnv p Int

           -> Int -> LDSL p Int -> LabelEnv p Int

           -> WireValuation p -> (String -> Proof)
           -> DSLValue p

           -> TyEnv' Int -> TyEnv' Int
           -> (Int -> Proof)

           -> Proof
uniqueBool m0 m' b e ρ λ m e' λ' σ π v γ γ' h_boolean = trivial


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
