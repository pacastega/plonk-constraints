{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--ple-with-undecided-guards" @-}
module WitnessGenProof.UniquenessLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import TypeAliases
import Utils
import DSL
import Label
import MapLemmas
import Language.Haskell.Liquid.ProofCombinators


{-@ reflect elemsSet @-}
elemsSet :: (Ord v) => M.Map k v -> S.Set v
elemsSet M.MTip = S.empty
elemsSet (M.MBin _ v m) = S.singleton v `S.union` elemsSet m


{-@ elementLemma2 :: key:k -> val:v -> m:{M.Map k v | M.lookup key m = Just val}
                  -> { S.member val (elemsSet m) } @-}
elementLemma2 :: Ord k => k -> v -> M.Map k v -> Proof
elementLemma2 k v (M.MBin k' v' m') =
  if k == k' then trivial else elementLemma2 k v m'


{-@ labelWFWire :: e:TypedDSL p -> m0:Nat
                -> m:{Nat | m >= m0} -> e':LDSL p (Btwn 0 m)
                -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 M.empty = (m,e',λ')}
                -> { S.isSubsetOf (wWiresE e') (wiresE e') } @-}
labelWFWire :: (Ord p, Fractional p) => DSL p -> Int
            -> Int -> LDSL p Int -> LabelEnv p Int -> Proof
labelWFWire e m0 m e' λ' = labelWFWire' e m0 M.empty m e' λ'


{-@ type EnvGE Λ2 Λ1 = s:{_ | M.member s Λ1}
                    -> { M.member s Λ2 && M.lookup' s Λ1 = M.lookup' s Λ2 } @-}


{-@ labelIncrEnv :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
                 -> m:{Nat | m >= m0} -> e':LDSL p (Btwn 0 m)
                 -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m,e',λ')}
                 -> MapGE λ' λ
                  / [size e] @-}
labelIncrEnv :: (Ord p, Fractional p) => DSL p -> Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int -> (String -> Proof)
labelIncrEnv e m0 λ m e' λ' x = case e of
  VAR s τ -> case M.lookup s λ of
    Nothing -> lookupLemma x λ -- x ∈ λ by hypothesis, so x ≠ s
    Just _ -> trivial
  CONST _ -> trivial
  BOOL  _ -> trivial

  UN op e1 -> case op of
    BoolToF -> labelIncrEnv e1 m0 λ m1 e1' λ1 x
      where (m1,e1',λ1) = label' e1 m0 λ
    ISZERO -> labelIncrEnv (UN (EQLC zero) e1) m0 λ m e' λ' x
    EQLC _ -> labelIncrEnv e1 m0 λ m1 e1' λ1 x
      where (m1,e1',λ1) = label' e1 m0 λ
    _ -> labelIncrEnv e1 m0 λ m1 e1' λ1 x
      where (m1,e1',λ1) = label' e1 m0 λ

  BIN op e1 e2 -> case op of
    DIV -> labelIncrEnv e1 m0 λ  m1 e1' λ1 x
        ?? labelIncrEnv e2 m1 λ1 m2 e2' λ2 x
      where (m1,e1',λ1) = label' e1 m0 λ
            (m2,e2',λ2) = label' e2 m1 λ1
    EQL -> labelIncrEnv (UN (EQLC zero) (BIN SUB e1 e2)) m0 λ m e' λ' x
    _ -> labelIncrEnv e1 m0 λ  m1 e1' λ1 x
      ?? labelIncrEnv e2 m1 λ1 m2 e2' λ2 x
      where (m1,e1',λ1) = label' e1 m0 λ
            (m2,e2',λ2) = label' e2 m1 λ1

  NIL _ -> trivial
  CONS e1 e2 -> labelIncrEnv e1 m0 λ  m1 e1' λ1 x
             ?? labelIncrEnv e2 m1 λ1 m2 e2' λ2 x
    where (m1,e1',λ1) = label' e1 m0 λ
          (m2,e2',λ2) = label' e2 m1 λ1



{-@ labelWFWire' :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
                 -> m:{Nat | m >= m0} -> e':LDSL p (Btwn 0 m)
                 -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m,e',λ')}
                 -> { S.isSubsetOf (elemsSet λ) (elemsSet λ')
                        && S.isSubsetOf (elemsSet λ') (S.union (elemsSet λ) (wiresE e'))
                        && S.isSubsetOf (wWiresE e') (elemsSet λ')}
                  / [size e] @-}
labelWFWire' :: (Ord p, Fractional p) => DSL p -> Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int -> Proof
labelWFWire' e m0 λ m e' λ' = case e of
  VAR s τ -> case M.lookup s λ of
    Nothing -> trivial
    Just j -> elementLemma2 s j λ -- ? liquidAssert (S.member j (elemsSet λ))
  CONST _ -> trivial
  BOOL  _ -> trivial

  UN op e1 -> case op of
    BoolToF -> labelWFWire' e1 m0 λ m1 e1' λ1
      where (m1,e1',λ1) = label' e1 m0 λ
    ISZERO -> labelWFWire' (UN (EQLC zero) e1) m0 λ m e' λ'
    EQLC _ -> labelWFWire' e1 m0 λ m1 e1' λ1
      where (m1,e1',λ1) = label' e1 m0 λ
    _ -> labelWFWire' e1 m0 λ m1 e1' λ1
      where (m1,e1',λ1) = label' e1 m0 λ

  BIN op e1 e2 -> case op of
    DIV -> labelWFWire' e1 m0 λ  m1 e1' λ1
        ?? labelWFWire' e2 m1 λ1 m2 e2' λ2
      where (m1,e1',λ1) = label' e1 m0 λ
            (m2,e2',λ2) = label' e2 m1 λ1
    EQL -> labelWFWire' (UN (EQLC zero) (BIN SUB e1 e2)) m0 λ m e' λ'
    _ -> labelWFWire' e1 m0 λ  m1 e1' λ1
      ?? labelWFWire' e2 m1 λ1 m2 e2' λ2
      where (m1,e1',λ1) = label' e1 m0 λ
            (m2,e2',λ2) = label' e2 m1 λ1

  NIL _ -> trivial
  CONS e1 e2 -> labelWFWire' e1 m0 λ  m1 e1' λ1
             ?? labelWFWire' e2 m1 λ1 m2 e2' λ2
    where (m1,e1',λ1) = label' e1 m0 λ
          (m2,e2',λ2) = label' e2 m1 λ1
