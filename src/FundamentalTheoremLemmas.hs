{-# LANGUAGE CPP #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
module FundamentalTheoremLemmas where

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


--TODO: move this to Semantics
{-@ reflect holds @-}
{-@ holds :: a:Assertion p -> NameValuation p -> Bool @-}
holds :: (Fractional p, Eq p) => Assertion p -> NameValuation p -> Bool
holds a ρ = case a of
  NZERO e1 | Just _ <- inferType e1
           , Just (VF v1) <- eval e1 ρ
          -> v1 /= 0
  BOOLEAN e1 | Just _ <- inferType e1
             , Just (VF v1) <- eval e1 ρ
            -> boolean v1
  EQA e1 e2 | Just _ <- inferType e1 , Just _ <- inferType e2
            , Just (VF v1) <- eval e1 ρ
            , Just (VF v2) <- eval e2 ρ
           -> v1 == v2
  _ -> False


{-@ fundamentalThmA1' :: m0:Nat -> a:Assertion p
                     -> ρ:{NameValuation p | holds a ρ}

                     -> m:{Nat | m0 <= m}
                     -> a':LAss p (Btwn 0 m)
                     -> λ:{LabelEnv p (Btwn 0 m) |
                              labelAssertion a m0 M.MTip = (m, a', λ)}

                     -> (σ::{σ:WireValuation p m | coherentA m a' σ},
                         x:{String | M.member x λ} ->
                            { v:() | M.lookup x ρ = M.lookup (M.lookup' x λ) σ }) @-}
fundamentalThmA1' :: (Fractional p, Ord p) => Int -> Assertion p
                 -> NameValuation p

                 -> Int -> LAss p Int -> LabelEnv p Int

                 -> (WireValuation p, String -> Proof)
fundamentalThmA1' m0 a ρ m a' λ = case a of
  NZERO e1 -> (σ, π) where
    λ0 = M.MTip
    σ0 = M.MTip

    (m1,e1',λ1) = label' e1 m0 λ0

    wf = labelWF e1 m0 λ0 m1 e1' λ
    -- wt = labelTyped e1 m0 λ0 m1 e1' λ

    v1 = case eval e1 ρ of Just v -> v
    v1' = case v1 of VF v -> v

    (LNZERO _ w) = a'

    σ1 = wf ?? wgCompleteE m0 e1 ρ v1 λ0 σ0 (\_ -> ()) m1 e1' λ1
    σ = if v1' /= 0 then (M.insert w (1/v1') σ1) else error ""

    {-@ π :: Agree λ ρ σ @-}
    π j = agreeLemma m0 m1 e1 ρ λ0 σ0 (\_ -> ()) λ1 e1' σ1 j
       ?? notElemLemma j w λ1

  BOOLEAN e1 -> (σ, π) where
    λ0 = M.MTip
    σ0 = M.MTip

    (m1,e1',λ1) = label' e1 m0 λ0

    wf = labelWF e1 m0 λ0 m1 e1' λ

    v1 = case eval e1 ρ of Just v -> v

    σ = wf ?? wgCompleteE m0 e1 ρ v1 λ0 σ0 (\_ -> ()) m1 e1' λ1

    {-@ π :: Agree λ ρ σ @-}
    π j = agreeLemma m0 m1 e1 ρ λ0 σ0 (\_ -> ()) λ1 e1' σ j

  EQA e1 e2 -> (σ, π2) where
    λ0 = M.MTip
    σ0 = M.MTip

    (m1,e1',λ1) = label' e1 m0 λ0
    (m2,e2',λ2) = label' e2 m1 λ1

    wf1 = labelWF e1 m0 λ0 m1 e1' λ1
    wf2 = labelWF e2 m1 λ1 m2 e2' λ

    v1 = case eval e1 ρ of Just v -> v
    v2 = case eval e2 ρ of Just v -> v

    σ1 = wf1 ?? wgCompleteE m0 e1 ρ v1 λ0 σ0 (\_ -> ()) m1 e1' λ1
    σ  = wf2 ?? wgCompleteE m1 e2 ρ v2 λ1 σ1 π1         m2 e2' λ

    {-@ π1 :: Agree λ1 ρ σ1 @-}
    π1 j = agreeLemma m0 m1 e1 ρ λ0 σ0 (\_ -> ()) λ1 e1' σ  j

    {-@ π2 :: Agree λ  ρ σ @-}
    π2 j = agreeLemma m1 m2 e2 ρ λ1 σ1 π1         λ2 e2' σ1 j


-- {-@ fundamentalThmA2' :: m0:Nat -> e:TypedDSL p
--                      -> ρ:NameValuation p

--                      -> m:{Nat | m0 <= m}
--                      -> e':{LDSL p (Btwn 0 m) | isJust (tyEnvE e' M.MTip)}
--                      -> λ:{LabelEnv p (Btwn 0 m) | label' e m0 M.MTip = (m, e', λ)}

--                      -> v:DSLValue p

--                      -> σ:{WireValuation p m | closedExpr m σ e'
--                                             && coherentE m e' σ
--                                             && evalWire m e' σ = v}
--                      -> Agree λ ρ σ

--                      -> { eval e ρ = Just v } @-}
-- fundamentalThmA2' :: (Fractional p, Ord p) => Int -> DSL p
--                  -> NameValuation p

--                  -> Int -> LDSL p Int -> LabelEnv p Int
--                  -> DSLValue p

--                  -> WireValuation p -> (String -> Proof)

--                  -> Proof
-- fundamentalThmA2' m0 e ρ m e' λ v σ π =
--   wf ?? evalWireUnique m0 m e ρ λ0 m e' λ σ π v γ0 γ h_bool
--   where
--     λ0 = M.MTip

--     γ0 :: TyEnv' γ0
--     γ0 = M.MTip

--     wf = labelWF e m0 λ0 m e' λ
--     wt = labelTyped e m0 λ0 m e' λ

--     γ = wt ?? case tyEnvE e' γ0 of Just g -> g

--     {-@ h_bool :: j:{Btwn 0 m | S.member j (elemsSet λ)
--                              && M.lookup j γ = Just TBool}
--                -> { boolean (M.lookup' j σ) } @-}
--     h_bool j = labelElems e m0 λ0 m e' λ
--             ?? liquidAssert (S.isSubsetOf (elemsSet λ) (S.union (elemsSet λ0) (wiresE e')))
--             ?? wt
--             ?? booleanProof' m σ e' γ0 γ j


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
