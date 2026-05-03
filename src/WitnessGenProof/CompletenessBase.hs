{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}

{-@ LIQUID "--cores=1" @-}

module WitnessGenProof.CompletenessBase where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import Utils
import TypeAliases

import Constraints
import DSL
import Label
import WitnessGeneration
import Semantics

import MapLemmas
import LabelingProof.LabelingLemmas
import WitnessGenProof.SemanticsLemmas

import Language.Haskell.Liquid.ProofCombinators


{-@ wgCompleteVar :: m0:Nat
                  -> s:Var -> τ:ScalarTy
                  -> e:{TypedDSL p | e = VAR s τ}

                  -> ρ:NameValuation p
                  -> v:{p | eval e ρ = Just (VF v)}
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> σ:WireValuation p m0

                  -> Agree λ ρ σ

                  -> m:{Nat | m >= m0}
                  -> e':{LDSL p (Btwn 0 m) | wfE e' && freshE e' σ}
                  -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                  -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                          && sigmaVar m e' σ' = VF v} @-}
wgCompleteVar :: (Fractional p, Ord p)
              => Int -> Var -> Ty -> DSL p
              -> NameValuation p -> p -> LabelEnv p Int -> WireValuation p
              -> (Var -> Proof)

              -> Int -> LDSL p Int -> LabelEnv p Int

              -> WireValuation p
wgCompleteVar m0 s τ e ρ v λ σ π m e' λ' = case M.lookup s ρ of
  Just value -> case M.lookup s λ of -- Is the variable labeled already?
    Nothing -> case τ of             -- NO: we get "LVAR s τ i"
      TF -> M.insert (outputWire e') value σ
      TBool -> if boolean value
               then M.insert (outputWire e') value σ
               else error "value ∈ {0,1} because eval succeeds"
    Just j -> elementLemma s j λ     -- YES: we get "LWIRE τ j"
           ?? π s ?? lookupLemma s λ -- value == ρ[s] == σ[Λ[s]] == σ[j]
           ?? evalVar s τ ρ v

           ?? elementLemma s value ρ ?? lookupLemma s ρ
           ?? elementLemma j value σ ?? lookupLemma j σ
           ?? case τ of
               TF -> σ
               TBool -> if boolean value then sigmaVarScalar m e' σ ?? σ
                        else error "value ∈ {0,1} because eval succeeds"


{-@ wgCompleteConst :: m0:Nat
                    -> x:p
                    -> e:{TypedDSL p | e = CONST x}

                    -> ρ:NameValuation p
                    -> v:{p | eval e ρ = Just (VF v)}
                    -> λ:LabelEnv p (Btwn 0 m0)
                    -> σ:WireValuation p m0

                    -> m:{Nat | m >= m0}
                    -> e':{LDSL p (Btwn 0 m) | wfE e' && freshE e' σ}
                    -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                    -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                            && sigmaVar m e' σ' = VF v} @-}
wgCompleteConst :: (Fractional p, Eq p)
                => Int -> p -> DSL p
                -> NameValuation p -> p -> LabelEnv p Int -> WireValuation p

                -> Int -> LDSL p Int -> LabelEnv p Int

                -> WireValuation p
wgCompleteConst m0 x e ρ v λ σ m e' λ' = M.insert (outputWire e') x σ


{-@ wgCompleteBool :: m0:Nat
                   -> b:Bool
                   -> e:{TypedDSL p | e = BOOL b}

                   -> ρ:NameValuation p
                   -> v:{p | eval e ρ = Just (VF v)}
                   -> λ:LabelEnv p (Btwn 0 m0)
                   -> σ:WireValuation p m0

                   -> m:{Nat | m >= m0}
                   -> e':{LDSL p (Btwn 0 m) | wfE e' && freshE e' σ}
                   -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                   -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                           && sigmaVar m e' σ' = VF v} @-}
wgCompleteBool :: (Fractional p, Eq p)
               => Int -> Bool -> DSL p
               -> NameValuation p -> p -> LabelEnv p Int -> WireValuation p

               -> Int -> LDSL p Int -> LabelEnv p Int

               -> WireValuation p
wgCompleteBool m0 b e ρ v λ σ m e' λ' =
  M.insert (outputWire e') (if b then 1 else 0) σ


{-@ typedScalarVar :: s:Var -> τ:ScalarTy
                   -> { scalar (VAR s τ) } @-}
typedScalarVar :: Var -> Ty -> Proof
typedScalarVar s τ = case τ of
  TF -> trivial
  TBool -> trivial

{-@ typedScalarConst :: x:p -> { scalar (CONST x) } @-}
typedScalarConst :: p -> Proof
typedScalarConst x = trivial

{-@ typedScalarBool :: b:Bool -> { scalar (BOOL b) } @-}
typedScalarBool :: Bool -> Proof
typedScalarBool b = trivial


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
