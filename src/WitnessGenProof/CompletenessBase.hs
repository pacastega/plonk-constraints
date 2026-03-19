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

import Language.Haskell.Liquid.ProofCombinators


{-@ wgCompleteVar :: m0:Nat -> m:{Nat | m >= m0}
                  -> s:Var
                  -> τ:ScalarTy
                  -> ρ:{NameValuation p | isJust (eval (VAR s τ) ρ)}
                  -> λ:LabelEnv p (Btwn 0 m0)
                  -> σ:WireValuation p m0

                  -> Agree λ ρ σ

                  -> λ':LabelEnv p (Btwn 0 m)
                  -> e':{LDSL p (Btwn 0 m) | freshE e' σ
                                 && label' (VAR s τ) m0 λ = (m, e', λ')}

                  -> { isJust (witnessGenE' m ρ σ e') } @-}
wgCompleteVar :: (Fractional p, Ord p)
              => Int -> Int -> Var -> Ty
              -> NameValuation p -> LabelEnv p Int -> WireValuation p

              -> (Var -> Proof)

              -> LabelEnv p Int
              -> LDSL p Int

              -> Proof
wgCompleteVar m0 m s τ ρ λ σ π λ' e' = case M.lookup s ρ of
  Nothing -> error "the variable is defined in ρ because eval succeeds"
  Just value -> case M.lookup s λ of -- Is the variable labeled already?
    Nothing -> case τ of             -- NO: we get "LVAR s τ i"
      TF -> trivial
      TBool -> if boolean value
               then trivial
               else error "the value is in {0,1} because eval succeeds"
    Just j -> elementLemma s j λ     -- YES: we get "LWIRE j"
            ? π s ? lookupLemma s λ
            ? case τ of
                TF -> witnessGenE' m ρ σ (LWIRE τ j) === Just σ *** QED
                TBool -> if boolean value
                         then witnessGenE' m ρ σ (LWIRE τ j) === Just σ *** QED
                         else error "the value is in {0,1} because eval succeeds"


{-@ wgCompleteConst :: m0:Nat -> m:{Nat | m >= m0}
                    -> x:p
                    -> ρ:{NameValuation p | isJust (eval (CONST x) ρ)}
                    -> λ:LabelEnv p (Btwn 0 m0)
                    -> σ:WireValuation p m0

                    -> Agree λ ρ σ

                    -> λ':LabelEnv p (Btwn 0 m)
                    -> e':{LDSL p (Btwn 0 m) | freshE e' σ
                                 && label' (CONST x) m0 λ = (m, e', λ')}

                    -> { isJust (witnessGenE' m ρ σ e') } @-}
wgCompleteConst :: (Fractional p, Ord p)
                => Int -> Int -> p
                -> NameValuation p -> LabelEnv p Int -> WireValuation p

                -> (Var -> Proof)

                -> LabelEnv p Int
                -> LDSL p Int

                -> Proof
wgCompleteConst m0 m x ρ λ σ π λ' e' = trivial


{-@ wgCompleteBool :: m0:Nat -> m:{Nat | m >= m0}
                   -> b:Bool
                   -> ρ:{NameValuation p | isJust (eval (BOOL b) ρ)}
                   -> λ:LabelEnv p (Btwn 0 m0)
                   -> σ:WireValuation p m0

                   -> Agree λ ρ σ

                   -> λ':LabelEnv p (Btwn 0 m)
                   -> e':{LDSL p (Btwn 0 m) | freshE e' σ
                                 && label' (BOOL b) m0 λ = (m, e', λ')}

                   -> { isJust (witnessGenE' m ρ σ e') } @-}
wgCompleteBool :: (Fractional p, Ord p)
               => Int -> Int -> Bool
               -> NameValuation p -> LabelEnv p Int -> WireValuation p

               -> (Var -> Proof)

               -> LabelEnv p Int
               -> LDSL p Int

               -> Proof
wgCompleteBool m0 m b ρ λ σ π λ' e' = if b then trivial else trivial


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
