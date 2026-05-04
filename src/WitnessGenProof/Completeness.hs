{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--fast" @-}
module WitnessGenProof.Completeness where

import Constraints
import TypeAliases
import DSL
import Semantics
import WitnessGeneration
import Label

import Utils

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import LabelingProof.LabelingLemmas
import LabelingProof.RecursiveLemmas
import LabelingProof.AgreeLemma

import WitnessGenProof.WitnessGenLemmas
import WitnessGenProof.SemanticsLemmas
import WitnessGenProof.CompletenessBase
import WitnessGenProof.CompletenessOps
import WitnessGenProof.CompletenessDiv
import WitnessGenProof.CompletenessVec

import Language.Haskell.Liquid.ProofCombinators


{-@ auxUn :: m0:Nat
          -> e1:TypedDSL p
          -> op:{UnOp p | wellTyped (UN op e1)}
          -> ρ:NameValuation p
          -> v:{DSLValue p | eval (UN op e1) ρ = Just v}
          -> λ:LabelEnv p (Btwn 0 m0)
          -> σ:WireValuation p m0

          -> Agree λ ρ σ

          -> m:{Nat | m >= m0}
          -> e':{LDSL p (Btwn 0 m) | freshE e' σ && wfE e'}
          -> λ':{LabelEnv p (Btwn 0 m) | label' (UN op e1) m0 λ = (m, e', λ')}

          -> { σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                   && sigmaVar m e' σ' = v }
           / [size (UN op e1), 0] @-}
auxUn :: (Fractional p, Ord p) => Int -> DSL p -> UnOp p
      -> NameValuation p -> DSLValue p
      -> LabelEnv p Int -> WireValuation p

      -> (String -> Proof)

      -> Int
      -> LDSL p Int
      -> LabelEnv p Int

      -> WireValuation p
auxUn m0 e1 op ρ v λ σ π m e' λ' = admit' m
  --                                  case op of
  -- ISZERO  -> admit' m
  --            -- wgCompleteE m0 m (UN (EQLC zero) e1) ρ λ σ π λ' e'
  -- EQLC k  -> admit' m
  --   --          case eval e1 ρ of
  --   -- Just _ -> wgCompleteE m0 m1 e1 ρ λ σ π λ1 e1' ? wgLemma m1 m ρ σ e1' ?
  --   --   case witnessGenE' m ρ σ e1' of Just _ -> trivial
  --   --   where (m1, e1', λ1) = label' e1 m0 λ
  -- BoolToF -> admit' m
  --            -- wgCompleteE m0 m e1 ρ λ σ π λ' e'
  -- _ -> σ' where
  --   (m1,e1',λ1) = label' e1 m0 λ
  --   v1 = evalUn e1 op ρ v

  --   wf1 = labelWF    e1 m0 λ m1 e1' λ1 -- e1' is well-formed
  --   wt1 = labelTyped e1 m0 λ m1 e1' λ1 -- e1' is well-typed

  --   size1 = sizeUn e1 op

  --   m_gt_m1 = labelIncUn op e1 m0 λ m1 e1' λ1 m e' λ'
  --   i = m_gt_m1 ?? labelUn m0 e1 λ op m1 e1' λ1 m e' λ'
  --     ? labelTyped (UN op e1) m0 λ m e' λ' -- e' is well-typed

  --   fresh1 = m_gt_m1 ?? freshUn m e1' op i σ
  --   σ1 = size1 ?? wf1 ?? wt1 ?? fresh1 ?? wgLemma m1 m ρ σ e1'
  --     ?? wgCompleteE m0 e1 ρ (VF v1) λ σ π m1 e1' λ1

  --   v' = typedScalarUn e1 op ?? evalScalar (UN op e1) ρ v -- VF v' == v
  --   σ' = m_gt_m1
  --     ?? sigmaVarLemma m1 m e1' σ1 -- sigmaVar ignores its first argument
  --     ?? wgCompleteUn m0 op e1 (UN op e1) ρ v1 v' λ σ
  --                     m1 e1' λ1 m e' λ' i σ1


{-@ auxBin :: m0:Nat
           -> e1:TypedDSL p -> e2:TypedDSL p
           -> op:{BinOp p | wellTyped (BIN op e1 e2)}
           -> ρ:NameValuation p
           -> v:{DSLValue p | eval (BIN op e1 e2) ρ = Just v}
           -> λ:LabelEnv p (Btwn 0 m0)
           -> σ:WireValuation p m0

           -> Agree λ ρ σ

           -> m:{Nat | m >= m0}
           -> e':{LDSL p (Btwn 0 m) | freshE e' σ && wfE e'}
           -> λ':{LabelEnv p (Btwn 0 m) | label' (BIN op e1 e2) m0 λ = (m, e', λ')}

           -> { σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                    && sigmaVar m e' σ' = v }
            / [size (BIN op e1 e2), 0] @-}
auxBin :: (Fractional p, Ord p) => Int -> DSL p -> DSL p -> BinOp p
       -> NameValuation p -> DSLValue p
       -> LabelEnv p Int -> WireValuation p

       -> (String -> Proof)

       -> Int
       -> LDSL p Int
       -> LabelEnv p Int

       -> WireValuation p
auxBin m0 e1 e2 op ρ v λ σ π m e' λ' = admit' m
  --                                      case op of
  -- DIV -> σ' where
  --   (m1,e1',λ1) = label' e1 m0 λ
  --   v1 = evalDiv1 e1 e2 ρ v

  --   (m2,e2',λ2) = label' e2 m1 λ1
  --   v2 = evalDiv2 e1 e2 ρ v

  --   wf1 = labelWF    e1 m0 λ m1 e1' λ1 -- e1' is well-formed
  --   wt1 = labelTyped e1 m0 λ m1 e1' λ1 -- e1' is well-typed

  --   wf2 = labelWF    e2 m1 λ1 m2 e2' λ2 -- e2' is well-formed
  --   wt2 = labelTyped e2 m1 λ1 m2 e2' λ2 -- e2' is well-typed

  --   size12 = sizeBin e1 e2 op

  --   m_gt_m2 = labelIncBin op e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'
  --   (w,i) = m_gt_m2 ?? labelDiv m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 m e' λ'
  --        ? labelTyped (BIN op e1 e2) m0 λ m e' λ' -- e' is well-typed

  --   fresh1 = m_gt_m2 ?? freshDiv1 m e1' e2' w i σ
  --   σ1 = size12 ?? wf1 ?? wt1 ?? fresh1 ?? wgLemma m1 m ρ σ e1'
  --     ?? wgCompleteE m0 e1 ρ (VF v1) λ σ π m1 e1' λ1

  --   π1 = wf1 ?? fresh1 ?? agreeLemma m0 m1 e1 ρ λ σ π λ1 e1' σ1

  --   fresh2 = freshDiv2 m ρ e1' e2' w i σ σ1
  --   σ2 = size12 ?? wf2 ?? wt2 ?? fresh2 ?? wgLemma m2 m ρ σ1 e2'
  --     ?? wgCompleteE m1 e2 ρ (VF v2) λ1 σ1 π1 m2 e2' λ2

  --   v' = typedScalarBin e1 e2 op ?? evalScalar (BIN op e1 e2) ρ v -- VF v' == v
  --   σ' = m_gt_m2
  --     ?? sigmaVarLemma m1 m e1' σ1 -- sigmaVar ignores its first argument
  --     ?? sigmaVarLemma m2 m e2' σ2 -- sigmaVar ignores its first argument
  --     ?? wgCompleteDiv m0 e1 e2 (BIN op e1 e2) ρ v1 v2 v' λ σ
  --                      m1 e1' λ1 m2 e2' λ2 m  e'  λ' w i σ1 σ2

  -- EQL -> admit' m
  -- _   -> σ' where

  --   (m1,e1',λ1) = label' e1 m0 λ
  --   v1 = evalBin1 e1 e2 op ρ v -- isJust (eval e1 ρ) && isJust (eval e2 ρ)

  --   (m2,e2',λ2) = label' e2 m1 λ1
  --   v2 = evalBin2 e1 e2 op ρ v -- isJust (eval e1 ρ) && isJust (eval e2 ρ)

  --   wf1 = labelWF    e1 m0 λ m1 e1' λ1 -- e1' is well-formed
  --   wt1 = labelTyped e1 m0 λ m1 e1' λ1 -- e1' is well-typed

  --   wf2 = labelWF    e2 m1 λ1 m2 e2' λ2 -- e2' is well-formed
  --   wt2 = labelTyped e2 m1 λ1 m2 e2' λ2 -- e2' is well-typed

  --   size12 = sizeBin e1 e2 op

  --   m_gt_m2 = labelIncBin op e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'
  --   i = m_gt_m2 ?? labelBin m0 e1 e2 λ op m1 e1' λ1 m2 e2' λ2 m e' λ'
  --     ? labelTyped (BIN op e1 e2) m0 λ m e' λ' -- e' is well-typed

  --   fresh1 = m_gt_m2 ?? freshBin1 m e1' e2' op i σ
  --   σ1 = size12 ?? wf1 ?? wt1 ?? fresh1 ?? wgLemma m1 m ρ σ e1'
  --     ?? wgCompleteE m0 e1 ρ (VF v1) λ σ π m1 e1' λ1

  --   π1 = wf1 ?? fresh1 ?? agreeLemma m0 m1 e1 ρ λ σ π λ1 e1' σ1

  --   fresh2 = freshBin2 m ρ e1' e2' op i σ σ1
  --   σ2 = size12 ?? wf2 ?? wt2 ?? fresh2 ?? wgLemma m2 m ρ σ1 e2'
  --     ?? wgCompleteE m1 e2 ρ (VF v2) λ1 σ1 π1 m2 e2' λ2

  --   v' = typedScalarBin e1 e2 op ?? evalScalar (BIN op e1 e2) ρ v -- VF v' == v
  --   σ' = m_gt_m2
  --     ?? sigmaVarLemma m1 m e1' σ1 -- sigmaVar ignores its first argument
  --     ?? sigmaVarLemma m2 m e2' σ2 -- sigmaVar ignores its first argument
  --     ?? wgCompleteBin m0 op e1 e2 (BIN op e1 e2) ρ v1 v2 v' λ σ
  --                      m1 e1' λ1 m2 e2' λ2 m  e'  λ' i σ1 σ2


{-@ auxCons :: m0:Nat
            -> e1:TypedDSL p -> e2:{TypedDSL p | wellTyped (CONS e1 e2)}
            -> ρ:NameValuation p
            -> v:{DSLValue p | eval (CONS e1 e2) ρ = Just v}
            -> λ:LabelEnv p (Btwn 0 m0)
            -> σ:WireValuation p m0

            -> Agree λ ρ σ

            -> m:{Nat | m >= m0}
            -> e':{LDSL p (Btwn 0 m) | freshE e' σ && wfE e'}
            -> λ':{LabelEnv p (Btwn 0 m) | label' (CONS e1 e2) m0 λ = (m, e', λ')}

            -> { σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                     && sigmaVar m e' σ' = v }
             / [size (CONS e1 e2), 0] @-}
auxCons :: (Fractional p, Ord p) => Int -> DSL p -> DSL p
        -> NameValuation p -> DSLValue p
        -> LabelEnv p Int -> WireValuation p

        -> (String -> Proof)

        -> Int -> LDSL p Int -> LabelEnv p Int

        -> WireValuation p
auxCons m0 e1 e2 ρ v λ σ π m e' λ' = σ' where
  (m1,e1',λ1) = label' e1 m0 λ
  v1 = evalCons1 e1 e2 ρ v -- isJust (eval e1 ρ) && isJust (eval e2 ρ)

  (m2,e2',λ2) = label' e2 m1 λ1
  v2 = evalCons2 e1 e2 ρ v -- isJust (eval e1 ρ) && isJust (eval e2 ρ)

  wf1 = labelWF    e1 m0 λ m1 e1' λ1 -- e1' is well-formed
  wt1 = labelTyped e1 m0 λ m1 e1' λ1 -- e1' is well-typed

  wf2 = labelWF    e2 m1 λ1 m2 e2' λ2 -- e2' is well-formed
  wt2 = labelTyped e2 m1 λ1 m2 e2' λ2 -- e2' is well-typed

  size12 = sizeCons e1 e2

  m_gt_m2 = labelIncCons e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'
  cons_thm = m_gt_m2 ?? labelCons m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 m e' λ'
    ? labelTyped (CONS e1 e2) m0 λ m e' λ' -- e' is well-typed

  fresh1 = m_gt_m2 ?? cons_thm ?? freshCons1 m e1' e2' σ
  σ1 = size12 ?? wf1 ?? wt1 ?? fresh1 ?? wgLemma m1 m ρ σ e1'
    ?? wgCompleteE m0 e1 ρ v1 λ σ π m1 e1' λ1

  π1 = wf1 ?? fresh1 ?? agreeLemma m0 m1 e1 ρ λ σ π λ1 e1' σ1

  fresh2 = cons_thm ?? freshCons2 m ρ e1' e2' σ σ1
  σ2 = size12 ?? wf2 ?? wt2 ?? fresh2 ?? wgLemma m2 m ρ σ1 e2'
    ?? wgCompleteE m1 e2 ρ v2 λ1 σ1 π1 m2 e2' λ2

  -- v' = typedScalarBin e1 e2 op ?? evalScalar (BIN op e1 e2) ρ v -- VF v' == v
  σ' = m_gt_m2
    ?? sigmaVarLemma m1 m e1' σ1 -- sigmaVar ignores its first argument
    ?? sigmaVarLemma m2 m e2' σ2 -- sigmaVar ignores its first argument
    ?? wgCompleteCons m0 e1 e2 (CONS e1 e2) ρ v1 v2 v λ σ
                      m1 e1' λ1 m2 e2' λ2 m  e'  λ' σ1 σ2


{-@ wgCompleteE :: m0:Nat
                -> e:TypedDSL p
                -> ρ:NameValuation p
                -> v:{DSLValue p | eval e ρ = Just v}
                -> λ:LabelEnv p (Btwn 0 m0)
                -> σ:WireValuation p m0

                -> Agree λ ρ σ

                -> m:{Nat | m >= m0}
                -> e':{LDSL p (Btwn 0 m) | freshE e' σ && wfE e'}
                -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                -> { σ':WireValuation p m | Just σ' = witnessGenE' m ρ σ e'
                                         && sigmaVar m e' σ' = v}
                 / [size e, 1] @-}
wgCompleteE :: (Fractional p, Ord p) => Int -> DSL p
            -> NameValuation p -> DSLValue p
            -> LabelEnv p Int -> WireValuation p

            -> (String -> Proof)

            -> Int
            -> LDSL p Int
            -> LabelEnv p Int

            -> WireValuation p
wgCompleteE m0 e ρ v λ σ π m e' λ' = case e of
  VAR s τ -> wgCompleteVar m0 s τ e ρ v' λ σ π m e' λ'
    where v' = typedScalarVar s τ ?? evalScalar e ρ v
  CONST x -> wgCompleteConst m0 x e ρ v' λ σ m e' λ'
    where v' = typedScalarConst x ?? evalScalar e ρ v
  BOOL b  -> wgCompleteBool m0 b e ρ v' λ σ m e' λ'
    where v' = typedScalarBool b ?? evalScalar e ρ v

  UN op e1 -> wellTypedUn e1 op ?? auxUn m0 e1 op ρ v λ σ π m e' λ'
  BIN op e1 e2 -> wellTypedBin e1 e2 op ?? auxBin m0 e1 e2 op ρ v λ σ π m e' λ'

  NIL τ -> wgCompleteNil m0 τ e ρ v λ σ m e' λ'
  CONS e1 e2 -> wellTypedCons e1 e2
             ?? auxCons m0 e1 e2 ρ v λ σ π m e' λ'


{-@ assume admit :: () -> { False } @-}
admit :: () -> ()
admit _ = ()

{-@ assume admit' :: m:Nat -> { σ:WireValuation p m | False } @-}
admit' :: (Eq p, Fractional p) => Int -> WireValuation p
admit' _ = M.MTip


{-@ assume myAssume :: b:Bool -> {b} @-}
myAssume :: Bool -> ()
myAssume _ = ()
