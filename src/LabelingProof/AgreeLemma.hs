{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--fast" @-}
{-@ LIQUID "--max-case-expand=0" @-}

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
import LabelingProof.LabelingVar
import LabelingProof.LabelingISZERO
import LabelingProof.LabelingEQLC
import LabelingProof.LabelingOps
import LabelingProof.LabelingDIV
import LabelingProof.LabelingEQL

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
           -> e':{LDSL p (Btwn 0 m) | freshE e' σ && wfE e'
                            && label' (BIN op p1 p2) m0 λ = (m, e', λ')}
           -> σ':{WireValuation p m | Just σ' = witnessGenE' m ρ σ e'}

           -> Agree λ' ρ σ'
            / [size (BIN op p1 p2), 0] @-}
auxBin :: (Fractional p, Eq p, Ord p)
       => Int -> Int -> DSL p -> DSL p -> BinOp p
       -> NameValuation p
       -> LabelEnv p Int
       -> WireValuation p

       -> (Var -> Proof)

       -> LabelEnv p Int
       -> LDSL p Int
       -> WireValuation p

       -> (String -> Proof)
auxBin m0 m p1 p2 op ρ λ σ π λ' e' σ' x = case op of
    -- DIV -> -- label2Inc DIV p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
    --   labelProofDIV m0 m1 m2 m p1 p2 ρ λ λ1 λ2 σ λ' p1' p2' e' σ' σ1 σ2 π2 x
    --   where (m1, p1', λ1) = label' p1 m0 λ
    --         (m2, p2', λ2) = label' p2 m1 λ1
    --         σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
    --         σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
    --         π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
    --         π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2

    EQL -> -- label2Inc EQL p1 p2 m0 λ m1 p1' λ1 m2 p2' λ2 m e' λ' ??
      agreeLemmaEQL m0 m1 m2 m p1 p2 ρ λ σ λ1 λ2 p1' σ1 p2' σ2 λ' e' σ' π2 x
      where (m1, p1', λ1) = label' p1 m0 λ
            (m2, p2', λ2) = label' p2 m1 λ1
            σ1 = case witnessGenE' m1 ρ σ  p1' ? wgLemma m1 m ρ σ  p1' of Just s -> s
            σ2 = case witnessGenE' m2 ρ σ1 p2' ? wgLemma m2 m ρ σ1 p2' of Just s -> s
            π1 = agreeLemma m0 m1 p1 ρ λ  σ  π  λ1 p1' σ1
            π2 = agreeLemma m1 m2 p2 ρ λ1 σ1 π1 λ2 p2' σ2
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
               -> e':{LDSL p (Btwn 0 m) | freshE e' σ
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
agreeLemma m0 m e ρ λ σ π λ' e' σ' x = labelWF e m0 λ m e' λ' ?? case e of
  VAR s τ -> agreeLemmaVar m0 m s τ ρ λ σ π λ' e' σ' x
  CONST _ -> π x ? notElemLemma x (outputWire e') λ

  BOOL b -> case b of
    True -> π x ? notElemLemma x (outputWire e') λ
    False -> π x ? notElemLemma x (outputWire e') λ

  UN  op p1    -> admit () -- auxUn  m0 m p1    op ρ λ σ π λ' e' σ' x
  BIN op p1 p2 -> auxBin m0 m p1 p2 op ρ λ σ π λ' e' σ' x

  NIL _ -> error "this theorem only talks about scalars"
  CONS _ _ -> error "this theorem only talks about scalars"


{-@ assume admit :: () -> { False } @-}
admit :: () -> ()
admit _ = ()
