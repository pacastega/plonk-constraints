{-# LANGUAGE CPP #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
module FundamentalTheorem where

import Constraints
import TypeAliases
import DSL
import Semantics
import Label
import WitnessGeneration

import Utils

import BooleanProof hiding (foo, barOp)

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import MapLemmas
import LabelingProof.LabelingLemmas
import LabelingProof.AgreeLemma
import WitnessGenProof.UniquenessLemmas
import WitnessGenProof.Soundness
import WitnessGenProof.Completeness
import WitnessGenProof.Uniqueness

import Language.Haskell.Liquid.ProofCombinators


{-@ fundamentalThmA :: m0:Nat -> e:TypedDSL p
                   -> ρ:NameValuation p

                   -> m:{Nat | m0 <= m}
                   -> e':LDSL p (Btwn 0 m)
                   -> λ:{LabelEnv p (Btwn 0 m) | label' e m0 M.MTip = (m, e', λ)}

                   -> v:{DSLValue p | eval e ρ = Just v}

                   -> (σ::{σ:WireValuation p m | coherentE m e' σ
                                              && evalWire m e' σ = v},
                       x:{String | M.member x λ} ->
                          { v:() | M.lookup x ρ = M.lookup (M.lookup' x λ) σ }) @-}
fundamentalThmA :: (Fractional p, Ord p) => Int -> DSL p
               -> NameValuation p

               -> Int -> LDSL p Int -> LabelEnv p Int
               -> DSLValue p

               -> (WireValuation p, String -> Proof)
fundamentalThmA m0 e ρ m e' λ v = ( σ ? sound
                                  , agreeLemma m0 m e ρ λ0 σ0 (\_ -> ()) λ e' σ )
  where
    λ0 = M.MTip
    σ0 = M.MTip

    wf = labelWF e m0 λ0 m e' λ
    wt = labelTyped e m0 λ0 m e' λ
    sound = wf ?? wt ?? wgSoundE m ρ σ0 e' σ
    σ = wf ?? wgCompleteE m0 e ρ v λ0 σ0 (\_ -> ()) m e' λ


{-@ fundamentalThmB :: m0:Nat -> e:TypedDSL p
                    -> ρ:NameValuation p

                    -> m:{Nat | m0 <= m}
                    -> e':{LDSL p (Btwn 0 m) | isJust (tyEnv' e')}
                    -> λ:{LabelEnv p (Btwn 0 m) | label' e m0 M.MTip = (m, e', λ)}

                    -> v:DSLValue p

                    -> σ:{WireValuation p m | closedExpr m σ e'
                                           && coherentE m e' σ
                                           && evalWire m e' σ = v}
                    -> Agree λ ρ σ

                    -> { eval e ρ = Just v } @-}
fundamentalThmB :: (Fractional p, Ord p) => Int -> DSL p
                -> NameValuation p

                -> Int -> LDSL p Int -> LabelEnv p Int
                -> DSLValue p

                -> WireValuation p -> (String -> Proof)

                -> Proof
fundamentalThmB m0 e ρ m e' λ v σ π =
  wf ?? evalWireUnique m0 m e ρ λ0 m e' λ σ π v γ0 γ h_bool
  where
    λ0 = M.MTip

    γ0 :: TyEnv' γ0
    γ0 = M.MTip

    wf = labelWF e m0 λ0 m e' λ
    wt = labelTyped e m0 λ0 m e' λ

    γ = wt ?? case tyEnvE e' γ0 of Just g -> g

    {-@ h_bool :: j:{Btwn 0 m | S.member j (elemsSet λ)
                             && M.lookup j γ = Just TBool}
               -> { boolean (M.lookup' j σ) } @-}
    h_bool j = labelWFWire' e m0 λ0 m e' λ
            ?? liquidAssert (S.isSubsetOf (elemsSet λ) (S.union (elemsSet λ0) (wiresE e')))
            ?? wt
            ?? booleanProof' m σ e' γ0 γ j


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
