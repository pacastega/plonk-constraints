{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--fast" @-}
{-@ LIQUID "--linear" @-}

{-@ LIQUID "--no-termination" @-}

module LabelingProof.AgreeLemma where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import Utils
import TypeAliases

import Vec
import DSL
import Label
import WitnessGeneration
import Semantics

import MapLemmas

import WitnessGenProof.WitnessGenLemmas

import LabelingProof.LabelingLemmas
-- import LabelingProof.LabelingVar
-- import LabelingProof.LabelingISZERO
-- import LabelingProof.LabelingEQLC
import LabelingProof.LabelingOps
import LabelingProof.LabelingDIV
import LabelingProof.LabelingEQL
import LabelingProof.RecursiveLemmas

import Language.Haskell.Liquid.ProofCombinators


-- {-@ auxUn :: m0:Nat -> m:{Nat | m >= m0}
--           -> p1:ScalarDSL p
--           -> op:{UnOp p | wellTyped (UN op p1)}
--           -> ρ:NameValuation p
--           -> λ:LabelEnv p (Btwn 0 m0)
--           -> σ:WireValuation p m0

--           -> Agree λ ρ σ

--           -> λ':LabelEnv p (Btwn 0 m)
--           -> e':{LDSL p (Btwn 0 m) | freshE e' σ && wfE e'
--                                && label' (UN op p1) m0 λ = (m, e', λ')}
--           -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}

--           -> Agree λ' ρ σ'
--            / [size (UN op p1), 0] @-}
-- auxUn :: (Fractional p, Eq p, Ord p)
--       => Int -> Int -> DSL p -> UnOp p
--       -> NameValuation p
--       -> LabelEnv p Int
--       -> WireValuation p

--       -> (Var -> Proof)

--       -> LabelEnv p Int
--       -> LDSL p Int
--       -> WireValuation p

--       -> (String -> Proof)
-- auxUn m0 m p1 op ρ λ σ π λ' e' σ' x = case op of
--   ISZERO -> agreeLemmaISZERO m0 m1 m p1 ρ λ λ1 σ π λ' p1' e' σ' σ1 π1 x
--     where (m1, ps1, λ1) = label' p1 m0 λ
--           p1' = case ps1 of [x] -> x
--           σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
--           π1 = agreeLemma m0 m1 p1 ρ λ σ π λ1 p1' σ1
--           (LEQLC _ _ w i) = e'

--   EQLC k -> agreeLemmaEQLC m0 m1 m k p1 ρ λ λ1 σ λ' p1' e' σ' σ1 π1 x
--     where (m1, ps1, λ1) = label' p1 m0 λ
--           p1' = case ps1 of [x] -> x
--           σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
--           π1 = agreeLemma m0 m1 p1 ρ λ σ π λ1 p1' σ1

--   BoolToF -> π1 x
--     where (m1, ps1, λ1) = label' p1 m0 λ
--           p1' = case ps1 of [x] -> x
--           σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
--           π1 = agreeLemma m0 m1 p1 ρ λ σ π λ1 p1' σ1

--   ADDC k -> agreeLemmaUn m0 m1 m p1 op ρ λ λ1 σ λ' p1' e' σ' σ1 π1 x
--     where (m1, ps1, λ1) = label' p1 m0 λ
--           p1' = case ps1 of [x] -> x
--           σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
--           π1 = agreeLemma m0 m1 p1 ρ λ σ π λ1 p1' σ1

--   MULC k -> agreeLemmaUn m0 m1 m p1 op ρ λ λ1 σ λ' p1' e' σ' σ1 π1 x
--     where (m1, ps1, λ1) = label' p1 m0 λ
--           p1' = case ps1 of [x] -> x
--           σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
--           π1 = agreeLemma m0 m1 p1 ρ λ σ π λ1 p1' σ1

--   NOT -> agreeLemmaUn m0 m1 m p1 op ρ λ λ1 σ λ' p1' e' σ' σ1 π1 x
--     where (m1, ps1, λ1) = label' p1 m0 λ
--           p1' = case ps1 of [x] -> x
--           σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
--           π1 = agreeLemma m0 m1 p1 ρ λ σ π λ1 p1' σ1

--   UnsafeNOT -> agreeLemmaUn m0 m1 m p1 op ρ λ λ1 σ λ' p1' e' σ' σ1 π1 x
--     where (m1, ps1, λ1) = label' p1 m0 λ
--           p1' = case ps1 of [x] -> x
--           σ1 = case witnessGenE' m1 ρ σ p1' ? wgLemma m1 m ρ σ p1' of Just s -> s
--           π1 = agreeLemma m0 m1 p1 ρ λ σ π λ1 p1' σ1



{-@ auxBin :: m0:Nat -> m:{Nat | m >= m0}
           -> p1:TypedDSL p -> p2:TypedDSL p
           -> op:{BinOp p | wellTyped (BIN op p1 p2)}
           -> ρ:NameValuation p
           -> λ:LabelEnv p (Btwn 0 m0)
           -> σ:WireValuation p m0

           -> Agree λ ρ σ

           -> λ':LabelEnv p (Btwn 0 m)
           -> e':{TypedLDSL p (Btwn 0 m) | freshE e' σ && wfE e'
                            && label' (BIN op p1 p2) m0 λ = (m, e', λ')}
           -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}

           -> Agree λ' ρ σ'
            / [size (BIN op p1 p2), 0] @-}
auxBin :: forall p. (Fractional p, Eq p, Ord p)
       => Int -> Int -> DSL p -> DSL p -> BinOp p
       -> NameValuation p
       -> LabelEnv p Int
       -> WireValuation p

       -> (Var -> Proof)

       -> LabelEnv p Int
       -> LDSL p Int
       -> WireValuation p

       -> (String -> Proof)
auxBin m0 m p1 p2 op ρ λ σ π λ' e' σ' x =
  let (m1, p1', λ1) = label' p1 m0 λ
      (m2, p2', λ2) = label' p2 m1 λ1
      m_gt_m1_m2 = label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ'

  in case op of
    DIV -> labelProofDIV m0 m1 m2 m p1 p2 ρ λ λ1 λ2 σ λ' p1' p2' e' σ' σ1 σ2 π2 x
      where σ1 = m_gt_m1_m2 ?? σ1Div m1 m ρ σ p1' p2' w i e' σ'
            σ2 = m_gt_m1_m2 ?? σ2Div m2 m ρ σ p1' p2' w i e' σ' σ1

            -- e' == LDIV p1' p2' w i
            (w,i) = labelDiv m0 p1 p2 λ m1 p1' λ1 m2 p2' λ2 m e' λ'

            π1 = wfDiv p1' p2' w i           -- p1' is well typed and well formed
              ?? wgDivFresh1 m p1' p2' w i σ -- p1' is fresh w.r.t. σ
              ?? wgLemma m1 m ρ σ p1'        -- using m and m1 yield the same output
              ?? agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1 -- IH 1

            π2 = wfDiv p1' p2' w i                -- p2' is well typed and well formed
              ?? wgDivFresh2 m ρ p1' p2' w i σ σ1 -- p2' is fresh w.r.t. σ1
              ?? wgLemma m2 m ρ σ1 p2'            -- using m and m2 yield the same result
              ?? agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2 -- IH 2

    EQL -> agreeLemmaEQL m0 m1 m2 m p1 p2 ρ λ σ λ1 λ2 p1' σ1 p2' σ2 λ' e' σ' π2 x
      where σ1 = m_gt_m1_m2 ?? σ1Eql m1 m ρ σ p1' p2' d w i e' σ'
            σ2 = m_gt_m1_m2 ?? σ2Eql m2 m ρ σ p1' p2' d w i e' σ' σ1

            -- e' == EQLC (LBIN SUB p1' p2' d) 0 w i
            (d,w,i) = labelEql m0 p1 p2 λ m1 p1' λ1 m2 p2' λ2 m e' λ'

            π1 = wfEql p1' p2' d w i
              ?? wgEqlFresh1 m p1' p2' d w i σ
              ?? wgLemma m1 m ρ σ p1'
              ?? agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1

            π2 = wfEql p1' p2' d w i
              ?? wgEqlFresh2 m ρ p1' p2' d w i σ σ1
              ?? wgLemma m2 m ρ σ1 p2'
              ?? agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    _ -> agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
      where σ1 = m_gt_m1_m2 ?? σ1Bin m1 m ρ σ p1' p2' op i e' σ'
            σ2 = m_gt_m1_m2 ?? σ2Bin m2 m ρ σ p1' p2' op i e' σ' σ1

            -- e' = LBIN op p1' p2' i
            i = labelBin m0 p1 p2 λ op m1 p1' λ1 m2 p2' λ2 m e' λ'

            π1 = wfBin p1' p2' op i
              ?? wgBinFresh1 m p1' p2' op i σ
              ?? wgLemma m1 m ρ σ p1'
              ?? agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1

            π2 = wfBin p1' p2' op i
              ?? wgBinFresh2 m ρ p1' p2' op i σ σ1
              ?? wgLemma m2 m ρ σ1 p2'
              ?? agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2


{-@ agreeLemma :: m0:Nat -> m:{Nat | m >= m0}
               -> e:TypedDSL p
               -> ρ:NameValuation p
               -> λ:LabelEnv p (Btwn 0 m0)
               -> σ:WireValuation p m0

               -> Agree λ ρ σ

               -> λ':LabelEnv p (Btwn 0 m)
               -> e':{LDSL p (Btwn 0 m) | freshE e' σ && wfE e'
                                       && label' e m0 λ = (m, e', λ')}
               -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}

               -> Agree λ' ρ σ'
               / [size e, 1] @-}
agreeLemma :: (Fractional p, Eq p, Ord p)
           => Int -> Int -> DSL p
           -> NameValuation p
           -> LabelEnv p Int
           -> WireValuation p

           -> (Var -> Proof)

           -> LabelEnv p Int
           -> LDSL p Int
           -> WireValuation p

           -> (Var -> Proof)
agreeLemma m0 m e ρ λ σ π λ' e' σ' x = case e of
   -- labelWF e m0 λ m e' λ' ??
  VAR s τ -> admit () -- agreeLemmaVar m0 m s τ ρ λ σ π λ' e' σ' x
  CONST _ -> admit () -- π x ? notElemLemma x (outputWire e') λ

  BOOL b -> admit () -- case b of
    -- True -> π x ? notElemLemma x (outputWire e') λ
    -- False -> π x ? notElemLemma x (outputWire e') λ

  UN  op p1    -> admit () -- auxUn  m0 m p1    op ρ λ σ π λ' e' σ' x
  BIN op p1 p2 -> wellTypedBin p1 p2 op
               ?? labelTyped e m0 λ m e' λ'
               ?? auxBin m0 m p1 p2 op ρ λ σ π λ' e' σ' x

  NIL _ -> admit () -- error "this theorem only talks about scalars"
  CONS _ _ -> admit () -- error "this theorem only talks about scalars"


{-@ assume admit :: () -> { False } @-}
admit :: () -> ()
admit _ = ()

{-@ assume admit' :: b:Bool -> { b } @-}
admit' :: Bool -> ()
admit' _ = ()
