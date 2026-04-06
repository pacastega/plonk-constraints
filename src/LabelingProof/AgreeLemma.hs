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
-- import LabelingProof.LabelingOps
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
           -> p1:ScalarDSL p -> p2:ScalarDSL p
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
  wellTypedBin p1 p2 op ??
  case op of
    --TODO: fix this format (?? at the beginning of the lines)
    DIV -> m_gt_m1_m2 ??
      liquidAssert (m > m1) ??
      labelProofDIV m0 m1 m2 m p1 p2 ρ λ λ1 λ2 σ λ' p1' p2' e' σ' σ1 σ2 π2 x
      where
            (m1, p1', λ1) = label' p1 m0 λ
            (m2, p2', λ2) = label' p2 m1 λ1

            {-@ m_gt_m1_m2 :: { m > m1 && m > m2 } @-}
            m_gt_m1_m2 :: Proof
            m_gt_m1_m2 = label2Inc DIV p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ'

            -- {-@ σ1 :: {σ1:WireValuation p m1 | Just σ1 = witnessGenE' m ρ σ p1'} @-}
            -- σ1 :: WireValuation p
            σ1 = m_gt_m1_m2
              ?? wgDivFresh1 m p1' p2' w i σ
              ?? wgDiv1 m1 m ρ σ p1' p2' w i e' σ'

            -- {-@ σ2 :: {σ2:WireValuation p m2 | Just σ2 = witnessGenE' m ρ σ1 p2'} @-}
            -- σ2 :: WireValuation p
            σ2 = m_gt_m1_m2
              ?? wgDivFresh2 m ρ p1' p2' w i σ σ1
              ?? wgDiv2 m2 m ρ σ p1' p2' w i e' σ' σ1

            {-@ p2_p1_wf :: { wfE p1' && wfE p2' } @-}
            p2_p1_wf :: Proof
            p2_p1_wf = wfDiv p1' p2' w i

            (w,i) = labelDiv m0 p1 p2 λ m1 p1' λ1 m2 p2' λ2 m e' λ'

            π1 = p2_p1_wf
              ?? wtDiv p1' p2' w i
              ?? wgLemma m1 m ρ σ p1'
              ?? agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
            π2 = p2_p1_wf
              ?? wtDiv p1' p2' w i
              ?? wgLemma m2 m ρ σ1 p2'
              ?? agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- EQL -> label2Inc EQL p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaEQL m0 m1 m2 m p1 p2 ρ λ σ λ1 λ2 p1' σ1 p2' σ2 λ' e' σ' π2 x
    --   where σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2
--------------------------------------------------------------------------------
    -- ADD -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- SUB -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- MUL -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- LINCOMB _ _ -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- AND -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- OR  -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- XOR -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- UnsafeAND -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- UnsafeOR  -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    -- UnsafeXOR -> -- label2Inc op p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   agreeLemmaBin m0 m1 m2 m p1 p2 op ρ λ λ1 λ2 σ π λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, ps1, λ1) = label' p1 m0 λ
    --         (m2, ps2, λ2) = label' p2 m1 λ1
    --         p1' = case ps1 of [x] -> x
    --         p2' = case ps2 of [x] -> x
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    _ -> admit ()

{-@ agreeLemma :: m0:Nat -> m:{Nat | m >= m0}
               -> e:ScalarDSL p
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
  BIN op p1 p2 -> admit () -- auxBin m0 m p1 p2 op ρ λ σ π λ' e' σ' x

  NIL _ -> admit () -- error "this theorem only talks about scalars"
  CONS _ _ -> admit () -- error "this theorem only talks about scalars"


{-@ assume admit :: () -> { False } @-}
admit :: () -> ()
admit _ = ()

{-@ assume admit' :: b:Bool -> { b } @-}
admit' :: Bool -> ()
admit' _ = ()
