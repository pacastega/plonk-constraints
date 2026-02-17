{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.SoundnessBase where

import Constraints
import TypeAliases
import DSL
import Semantics
import WitnessGeneration

import Utils

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import Language.Haskell.Liquid.ProofCombinators


{-@ wgSoundWire :: m:Nat
                -> ρ:NameValuation p
                -> σ:WireValuation p m

                -> τ:ScalarTy -> {i:Btwn 0 m | freshE (LWIRE τ i) σ}

                -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ (LWIRE τ i)}
                -> { coherentE m (LWIRE τ i) σ' } @-}
wgSoundWire :: (Eq p, Fractional p)
            => Int -> NameValuation p -> WireValuation p
            -> Ty -> Int
            -> WireValuation p -> Proof
wgSoundWire m ρ σ τ i σ' = trivial


{-@ wgSoundVar :: m:Nat
               -> ρ:NameValuation p
               -> σ:WireValuation p m

               -> s:Var -> τ:ScalarTy -> {i:Btwn 0 m | freshE (LVAR s τ i) σ}

               -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ (LVAR s τ i)}
               -> { coherentE m (LVAR s τ i) σ' } @-}
wgSoundVar :: (Eq p, Fractional p)
           => Int -> NameValuation p -> WireValuation p
           -> Var -> Ty -> Int
           -> WireValuation p -> Proof
wgSoundVar m ρ σ s τ i σ' = case τ of TF -> trivial; TBool -> trivial


{-@ wgSoundConst :: m:Nat
                 -> ρ:NameValuation p
                 -> σ:WireValuation p m

                 -> x:p -> {i:Btwn 0 m | freshE (LCONST x i) σ}

                 -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ (LCONST x i)}
                 -> { coherentE m (LCONST x i) σ' } @-}
wgSoundConst :: (Eq p, Fractional p)
             => Int -> NameValuation p -> WireValuation p
             -> p -> Int
             -> WireValuation p -> Proof
wgSoundConst m ρ σ x i σ' = trivial
