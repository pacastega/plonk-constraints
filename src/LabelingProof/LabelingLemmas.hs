{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module LabelingProof.LabelingLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import Utils
import TypeAliases

import Constraints
import DSL
import Label
import WitnessGeneration
import Semantics

import MapLemmas
import SetLemmas
import Language.Haskell.Liquid.ProofCombinators


-- ∀x ∈ dom(Λ) . ρ(x) = σ(Λ(x))
{-@ type Composable Ρ Λ Σ = var:{String | elem' var (M.keys Λ)}
                         -> {(M.lookup var Ρ = M.lookup (M.lookup' var Λ) Σ)} @-}

{-@ type Agree Λ Ρ Σ = var:{String | M.member var Λ}
                    -> {(M.lookup var Ρ = M.lookup (M.lookup' var Λ) Σ)} @-}



{-@ labelWF :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
            -> m:{Int | m >= m0} -> e':LDSL p Int
            -> λ':{LabelEnv p Int | label' e m0 λ = (m, e', λ')}
            -> { wfE e' }
             / [size e] @-}
labelWF :: (Num p, Ord p) => DSL p -> Int -> LabelEnv p Int
        -> Int -> LDSL p Int -> LabelEnv p Int
        -> Proof
labelWF e m0 λ m e' λ' = case e of
  VAR s _ -> case M.lookup s λ of
    Nothing -> trivial
    Just _  -> trivial
  CONST _ -> trivial
  BOOL True  -> trivial
  BOOL False -> trivial

  UN op e1 -> case op of
    BoolToF -> labelWF e1                  m0 λ m  e1' λ1
      where (i', e1', λ1) = label' e1 m0 λ
    ISZERO  -> labelWF (UN (EQLC zero) e1) m0 λ m  e'  λ'
    EQLC k  -> labelWF e1                  m0 λ i' e1' λ1
             ? ltLemma 0 i' used w' ? ltLemma 0 i' used i'
      where (i', e1', λ1) = label' e1 m0 λ
            w' = i'+1

            {-@ used :: S.Set (Btwn 0 i') @-}
            used :: S.Set Int
            used = wiresE e1'

    _ -> labelWF e1 m0 λ i' e1' λ1 ? ltLemma 0 i' used i'
      where (i', e1', λ1) = label' e1 m0 λ

            {-@ used :: S.Set (Btwn 0 i') @-}
            used :: S.Set Int
            used = wiresE e1'

  BIN op e1 e2 -> case op of
    DIV -> labelWF e1 m0 λ  i1 e1' λ1
         ? labelWF e2 i1 λ1 i2 e2' λ2
         ? ltLemma 0 i1 used1 i2 ? ltLemma i1 i2 used2 i2
         ? disjLemma 0 i1 i2 used1 used2
         ? ltLemma 0 i2 (used1 `S.union` used2) i
         ? ltLemma 0 i2 (used1 `S.union` used2) w
      where (i1, e1', λ1) = label' e1 m0 λ
            (i2, e2', λ2) = label' e2 i1 λ1

            (LDIV _ _ w i) = e'

            {-@ used1 :: S.Set (Btwn 0 i1) @-}
            used1 :: S.Set Int
            used1 = wiresE e1'

            {-@ used2 :: S.Set (Btwn i1 i2) @-}
            used2 :: S.Set Int
            used2 = wiresE e2'

    EQL -> labelWF e1 m0 λ  i1 e1' λ1
         ? labelWF e2 i1 λ1 i2 e2' λ2
         ? ltLemma 0 i1 used1 i2 ? ltLemma i1 i2 used2 i2
         ? disjLemma 0 i1 i2 used1 used2
         ? ltLemma 0 i2 (used1 `S.union` used2) i
         ? ltLemma 0 i2 (used1 `S.union` used2) w
      where (i1, e1', λ1) = label' e1 m0 λ
            (i2, e2', λ2) = label' e2 i1 λ1

            (LEQLC _ _ w i) = e'

            {-@ used1 :: S.Set (Btwn 0 i1) @-}
            used1 :: S.Set Int
            used1 = wiresE e1'

            {-@ used2 :: S.Set (Btwn i1 i2) @-}
            used2 :: S.Set Int
            used2 = wiresE e2'

    _ -> labelWF e1 m0 λ  i1 e1' λ1
       ? labelWF e2 i1 λ1 i2 e2' λ2
       ? ltLemma 0 i1 used1 i2 ? ltLemma i1 i2 used2 i2
       ? disjLemma 0 i1 i2 used1 used2
      where (i1, e1', λ1) = label' e1 m0 λ
            (i2, e2', λ2) = label' e2 i1 λ1

            {-@ used1 :: S.Set (Btwn 0 i1) @-}
            used1 :: S.Set Int
            used1 = wiresE e1'

            {-@ used2 :: S.Set (Btwn i1 i2) @-}
            used2 :: S.Set Int
            used2 = wiresE e2'

  NIL _ -> trivial
  CONS e es -> labelWF e  m0 λ  i1 e'  λ1
             ? labelWF es i1 λ1 i2 es' λ2
             ? disjLemma 0 i1 i2 usedH usedTs
    where (i1, e',  λ1) = label' e  m0 λ
          (i2, es', λ2) = label' es i1 λ1

          {-@ usedH :: S.Set (Btwn 0 i1) @-}
          usedH :: S.Set Int
          usedH = wiresE e'

          {-@ usedTs :: S.Set (Btwn i1 i2) @-}
          usedTs :: S.Set Int
          usedTs = wiresE es'

{-@ labelType :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
              -> m:Int -> e':LDSL p Int
              -> λ':{LabelEnv p Int | label' e m0 λ = (m, e', λ')}
              -> { inferType' e' = inferType e } @-}
labelType :: (Num p, Ord p) => DSL p -> Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
labelType e m0 λ _ _ _ = case label' e m0 λ of (_, e', _) -> trivial


{-@ labelTyped :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
               -> m:Int -> e':LDSL p Int
               -> λ':{LabelEnv p Int | label' e m0 λ = (m, e', λ')}
               -> { wellTyped' e' } @-}
labelTyped :: (Num p, Ord p) => DSL p -> Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Proof
labelTyped e m0 λ m e' λ' = case inferType e of
  Just _ -> labelType e m0 λ m e' λ'
