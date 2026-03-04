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

{-@ label1Inc :: op:UnOp p -> e1:{DSL p | wellTyped (UN op e1)} -> m0:Nat -> λ:LabelEnv p Int
              -> m1:Int -> e1':LDSL p Int -> λ1:{LabelEnv p Int | label' e1 m0 λ = (m1, mkList1 e1', λ1)}
              ->  m:Int ->  e':LDSL p Int -> λ':{LabelEnv p Int | label' (UN op e1) m0 λ = (m, mkList1 e', λ')}
              -> {m >= m1} @-}
label1Inc :: Num p => UnOp p -> DSL p -> Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
label1Inc op _ _ _ _ _ _ _ _ _ = case op of
  BoolToF -> ()
  ISZERO  -> ()
  EQLC _  -> ()
  _       -> ()

{-@ label2Inc :: op:{BinOp p | desugaredBinOp op || op == DIV}
              -> e1:DSL p -> e2:{DSL p | wellTyped (BIN op e1 e2)}
              -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

              -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
              -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, mkList1 e1', λ1)}

              -> m2:Nat -> e2':LDSL p (Btwn 0 m2)
              -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, mkList1 e2', λ2)}

              ->  m:Nat ->  e':LDSL p (Btwn 0 m)
              -> λ':{LabelEnv p (Btwn 0 m) | label' (BIN op e1 e2) m0 λ = (m, mkList1 e', λ')}
              -> {m > m2 && m2 >= m1} @-}
label2Inc :: (Num p, Ord p) => BinOp p -> DSL p -> DSL p -> Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
label2Inc op e1 e2 m0 λ m1 _e1' λ1 m2 _e2' _λ2 m _e' _λ'
  = trivial ? case label' e1 m0 λ  of (m1,_,_) -> m1
            ? case label' e2 m1 λ1 of (m2,_,_) -> m2
            ? case op of
                DIV -> liquidAssert (m == m2+2)
                _   -> liquidAssert (m == m2+1)


-- ∀x ∈ dom(Λ) . ρ(x) = σ(Λ(x))
{-@ type Composable Ρ Λ Σ = var:{String | elem' var (M.keys Λ)}
                         -> {(M.lookup var Ρ = M.lookup (M.lookup' var Λ) Σ)} @-}

{-@ type Agree Λ Ρ Σ = var:{String | M.member var Λ}
                    -> {(M.lookup var Ρ = M.lookup (M.lookup' var Λ) Σ)} @-}


{-@ wiresEsDistr :: es1:[LDSLI p i j] -> es2:[LDSLI p i j]
                 -> { wiresEs (append' es1 es2) = S.union (wiresEs es1) (wiresEs es2) } @-}
wiresEsDistr :: (Ord i) => [LDSLI p i j] -> [LDSLI p i j] -> Proof
wiresEsDistr [] es2 = trivial
wiresEsDistr (e:es) es2 = wiresEsDistr es es2


{-@ wfEsDistr :: es1:{[LDSL p i] | wfEs es1}
              -> es2:{[LDSL p i] | wfEs es2 && disjoint (wiresEs es1) (wiresEs es2)}
              -> { wfEs (append' es1 es2) } @-}
wfEsDistr :: (Ord i) => [LDSL p i] -> [LDSL p i] -> Proof
wfEsDistr [] es2 = trivial
wfEsDistr (e:es) es2 = wfEsDistr es es2 ? wiresEsDistr es es2


--TODO: this would all be easier if LDSL included vectors...
{-@ labelWF :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
            -> m:{Int | m >= m0} -> es':[LDSL p Int]
            -> λ':{LabelEnv p Int | label' e m0 λ = (m, es', λ')}
            -> { wfEs es' }
             / [size e] @-}
labelWF :: (Num p, Ord p) => DSL p -> Int -> LabelEnv p Int
        -> Int -> [LDSL p Int] -> LabelEnv p Int
        -> Proof
labelWF e m0 λ m es' λ' = case e of
  VAR s _ -> case M.lookup s λ of
    Nothing -> trivial
    Just _  -> trivial
  CONST _ -> trivial
  BOOL True  -> trivial
  BOOL False -> trivial

  UN op e1 -> case op of
    BoolToF -> labelWF e1                  m0 λ m  es' λ'
    ISZERO  -> labelWF (UN (EQLC zero) e1) m0 λ m  es' λ'
    EQLC k  -> labelWF e1                  m0 λ i' es1 λ1
             ? ltLemma 0 i' used w' ? ltLemma 0 i' used i'
      where (i', es1, λ1) = label' e1 m0 λ
            e1' = case es1 of [x] -> x
            w' = i'+1

            {-@ used :: S.Set (Btwn 0 i') @-}
            used :: S.Set Int
            used = wiresE e1'

    _ -> labelWF e1 m0 λ i' es1 λ1 ? ltLemma 0 i' used i'
      where (i', es1, λ1) = label' e1 m0 λ
            e1' = case es1 of [x] -> x

            {-@ used :: S.Set (Btwn 0 i') @-}
            used :: S.Set Int
            used = wiresE e1'

  BIN op e1 e2 -> case op of
    DIV -> labelWF e1 m0 λ  i1 es1 λ1
         ? labelWF e2 i1 λ1 i2 es2 λ2
         ? ltLemma 0 i1 used1 i2 ? ltLemma i1 i2 used2 i2
         ? disjLemma 0 i1 i2 used1 used2
         ? ltLemma 0 i2 (used1 `S.union` used2) i
         ? ltLemma 0 i2 (used1 `S.union` used2) w
      where (i1, es1, λ1) = label' e1 m0 λ
            (i2, es2, λ2) = label' e2 i1 λ1
            e1' = case es1 of [x] -> x
            e2' = case es2 of [x] -> x

            e'  = case es' of [x] -> x
            (LDIV _ _ w i) = e'

            {-@ used1 :: S.Set (Btwn 0 i1) @-}
            used1 :: S.Set Int
            used1 = wiresE e1'

            {-@ used2 :: S.Set (Btwn i1 i2) @-}
            used2 :: S.Set Int
            used2 = wiresE e2'

    EQL -> labelWF e1 m0 λ  i1 es1 λ1
         ? labelWF e2 i1 λ1 i2 es2 λ2
         ? ltLemma 0 i1 used1 i2 ? ltLemma i1 i2 used2 i2
         ? disjLemma 0 i1 i2 used1 used2
         ? ltLemma 0 i2 (used1 `S.union` used2) i
         ? ltLemma 0 i2 (used1 `S.union` used2) w
      where (i1, es1, λ1) = label' e1 m0 λ
            (i2, es2, λ2) = label' e2 i1 λ1
            e1' = case es1 of [x] -> x
            e2' = case es2 of [x] -> x

            e'  = case es' of [x] -> x
            (LEQLC _ _ w i) = e'

            {-@ used1 :: S.Set (Btwn 0 i1) @-}
            used1 :: S.Set Int
            used1 = wiresE e1'

            {-@ used2 :: S.Set (Btwn i1 i2) @-}
            used2 :: S.Set Int
            used2 = wiresE e2'

    _ -> labelWF e1 m0 λ  i1 es1 λ1
       ? labelWF e2 i1 λ1 i2 es2 λ2
       ? ltLemma 0 i1 used1 i2 ? ltLemma i1 i2 used2 i2
       ? disjLemma 0 i1 i2 used1 used2
      where (i1, es1, λ1) = label' e1 m0 λ
            (i2, es2, λ2) = label' e2 i1 λ1
            e1' = case es1 of [x] -> x
            e2' = case es2 of [x] -> x

            {-@ used1 :: S.Set (Btwn 0 i1) @-}
            used1 :: S.Set Int
            used1 = wiresE e1'

            {-@ used2 :: S.Set (Btwn i1 i2) @-}
            used2 :: S.Set Int
            used2 = wiresE e2'

  NIL _ -> trivial
  CONS e es -> labelWF e  m0 λ  i1 e'  λ1
             ? labelWF es i1 λ1 i2 es' λ2
             ? disjLemma 0 i1 i2 usedH usedTs ? wfEsDistr e' es'
    where (i1, e',  λ1) = label' e  m0 λ
          (i2, es', λ2) = label' es i1 λ1

          {-@ usedH :: S.Set (Btwn 0 i1) @-}
          usedH :: S.Set Int
          usedH = wiresEs e'

          {-@ usedTs :: S.Set (Btwn i1 i2) @-}
          usedTs :: S.Set Int
          usedTs = wiresEs es'
