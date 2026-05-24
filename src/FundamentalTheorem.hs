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
import WitnessGenProof.Soundness
import WitnessGenProof.Completeness

import WitnessGenProof.UniquenessBase
import WitnessGenProof.UniquenessOps
import WitnessGenProof.Uniqueness2 --FIXME: these lemmas should go somewhere else

import Language.Haskell.Liquid.ProofCombinators


--TODO: missing "agree" property
{-@ fundamentalThmA :: m0:Nat -> e:TypedDSL p
                   -> ρ:NameValuation p

                   -> m:{Nat | m0 <= m}
                   -> e':{TypedLDSL p (Btwn 0 m) | isJust (tyEnv' e')}
                   -> λ:{LabelEnv p (Btwn 0 m) | label' e m0 M.MTip = (m, e', λ)}

                   -> v:{DSLValue p | eval e ρ = Just v}

                   -> {σ:WireValuation p m | coherentE m e' σ
                                          && evalWire m e' σ = v} @-}
fundamentalThmA :: (Fractional p, Ord p) => Int -> DSL p
               -> NameValuation p

               -> Int -> LDSL p Int -> LabelEnv p Int
               -> DSLValue p

               -> WireValuation p
fundamentalThmA m0 e ρ m e' λ v = σ ? wgSoundE m ρ σ0 e' σ
  where
    λ0 = M.MTip
    σ0 = M.MTip

    wf = labelWF e m0 λ0 m e' λ
    σ = wf ?? wgCompleteE m0 e ρ v λ0 σ0 (\_ -> ()) m e' λ

--TODO: missing part B of the theorem
