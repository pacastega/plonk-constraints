{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.Uniqueness2 where

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
import LabelingProof.RecursiveLemmas hiding (foo, barOp)
import WitnessGenProof.WitnessGenLemmas
import WitnessGenProof.SemanticsLemmas
import WitnessGenProof.UniquenessLemmas

import Language.Haskell.Liquid.ProofCombinators


{-@ wiresUn :: e1:DSL p -> op:{UnOp p | wellTyped (UN op e1)}
            -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

            -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
            -> λ1:{LabelEnv p (Btwn 0 m1) | (m1,e1',λ1) = label' e1 m0 λ}

            -> m:Nat -> e':LDSL p (Btwn 0 m)
            -> λ':{LabelEnv p (Btwn 0 m) | (m,e',λ') = label' (UN op e1) m0 λ}

            -> { S.isSubsetOf (S.union (wiresE e1') (ptrsE e1'))
                              (S.union (wiresE e')  (ptrsE e') ) } @-}
wiresUn :: (Ord p, Num p)
        => DSL p -> UnOp p -> Int -> LabelEnv p Int
        -> Int -> LDSL p Int -> LabelEnv p Int
        -> Int -> LDSL p Int -> LabelEnv p Int
        -> Proof
wiresUn e1 op m0 λ m1 e1' λ1 m e' λ' = case op of
  ISZERO -> trivial
  EQLC _ -> trivial
  BoolToF -> trivial
  _ -> trivial

{-@ wiresBin :: e1:DSL p -> e2:DSL p -> op:{BinOp p | wellTyped (BIN op e1 e2)}
             -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

             -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | (m1,e1',λ1) = label' e1 m0 λ}

             -> m2:Nat -> e2':LDSL p (Btwn 0 m2)
             -> λ2:{LabelEnv p (Btwn 0 m2) | (m2,e2',λ2) = label' e2 m1 λ1}

             -> m:Nat -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) | (m,e',λ') = label' (BIN op e1 e2) m0 λ}

             -> { S.isSubsetOf (S.union (wiresE e1') (ptrsE e1'))
                               (S.union (wiresE e')  (ptrsE e') ) &&
                  S.isSubsetOf (S.union (wiresE e2') (ptrsE e2'))
                               (S.union (wiresE e')  (ptrsE e') ) } @-}
wiresBin :: (Ord p, Num p)
         => DSL p -> DSL p -> BinOp p -> Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Int -> LDSL p Int -> LabelEnv p Int
         -> Proof
wiresBin e1 e2 op m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ' = case op of
  DIV -> trivial
  EQL -> trivial
  _ -> trivial

{-@ wiresCons :: e1:DSL p -> e2:{DSL p | wellTyped (CONS e1 e2)}
              -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

              -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
              -> λ1:{LabelEnv p (Btwn 0 m1) | (m1,e1',λ1) = label' e1 m0 λ}

              -> m2:Nat -> e2':LDSL p (Btwn 0 m2)
              -> λ2:{LabelEnv p (Btwn 0 m2) | (m2,e2',λ2) = label' e2 m1 λ1}

              -> m:Nat -> e':LDSL p (Btwn 0 m)
              -> λ':{LabelEnv p (Btwn 0 m) | (m,e',λ') = label' (CONS e1 e2) m0 λ}

              -> { S.isSubsetOf (S.union (wiresE e1') (ptrsE e1'))
                                (S.union (wiresE e')  (ptrsE e') ) &&
                   S.isSubsetOf (S.union (wiresE e2') (ptrsE e2'))
                                (S.union (wiresE e')  (ptrsE e') ) } @-}
wiresCons :: (Ord p, Num p)
          => DSL p -> DSL p -> Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Int -> LDSL p Int -> LabelEnv p Int
          -> Proof
wiresCons e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ' = trivial


{-@ labelEnvUn :: e1:DSL p -> op:{UnOp p | wellTyped (UN op e1)}
               -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

               -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
               -> λ1:{LabelEnv p (Btwn 0 m1) | (m1,e1',λ1) = label' e1 m0 λ}

               -> m:Nat -> e':LDSL p (Btwn 0 m)
               -> λ':{LabelEnv p (Btwn 0 m) | (m,e',λ') = label' (UN op e1) m0 λ}

               -> { λ' = λ1 } @-}
labelEnvUn :: (Ord p, Num p)
           => DSL p -> UnOp p -> Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Proof
labelEnvUn e1 op m0 λ m1 e1' λ1 m e' λ' = case op of
  ISZERO -> trivial
  EQLC _ -> trivial
  BoolToF -> trivial
  _ -> trivial

{-@ labelEnvBin :: e1:DSL p -> e2:DSL p -> op:{BinOp p | wellTyped (BIN op e1 e2)}
                -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

                -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
                -> λ1:{LabelEnv p (Btwn 0 m1) | (m1,e1',λ1) = label' e1 m0 λ}

                -> m2:Nat -> e2':LDSL p (Btwn 0 m2)
                -> λ2:{LabelEnv p (Btwn 0 m2) | (m2,e2',λ2) = label' e2 m1 λ1}

                -> m:Nat -> e':LDSL p (Btwn 0 m)
                -> λ':{LabelEnv p (Btwn 0 m) | (m,e',λ') = label' (BIN op e1 e2) m0 λ}

                -> { λ' = λ2 } @-}
labelEnvBin :: (Ord p, Num p)
            => DSL p -> DSL p -> BinOp p -> Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Proof
labelEnvBin e1 e2 op m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ' = case op of
  DIV -> trivial
  EQL -> trivial
  _ -> trivial

{-@ labelEnvCons :: e1:DSL p -> e2:{DSL p | wellTyped (CONS e1 e2)}
                 -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)

                 -> m1:Nat -> e1':LDSL p (Btwn 0 m1)
                 -> λ1:{LabelEnv p (Btwn 0 m1) | (m1,e1',λ1) = label' e1 m0 λ}

                 -> m2:Nat -> e2':LDSL p (Btwn 0 m2)
                 -> λ2:{LabelEnv p (Btwn 0 m2) | (m2,e2',λ2) = label' e2 m1 λ1}

                 -> m:Nat -> e':LDSL p (Btwn 0 m)
                 -> λ':{LabelEnv p (Btwn 0 m) | (m,e',λ') = label' (CONS e1 e2) m0 λ}

                 -> { λ' = λ2 } @-}
labelEnvCons :: (Ord p, Num p)
             => DSL p -> DSL p -> Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Proof
labelEnvCons e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ' = trivial


{-@ coherentUn :: m0:Nat -> m':Nat -> op:UnOp p -> e1:TypedDSL p
               -> e:{TypedDSL p | e = UN op e1}
               -> λ:LabelEnv p (Btwn 0 m0)

               -> m:{Nat | m0 <= m && m <= m'}
               -> e':LDSL p (Btwn 0 m)
               -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

               -> m1:{Nat | m0 <= m1 && m1 <= m}
               -> e1':LDSL p (Btwn 0 m1)
               -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

               -> σ:{WireValuation p m' | closedExpr m' σ e'
                                       && coherentE m' e' σ}
               -> { closedExpr m' σ e1' && coherentE m' e1' σ } @-}
coherentUn :: (Num p, Ord p)
           => Int -> Int -> UnOp p -> DSL p -> DSL p -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> WireValuation p -> Proof
coherentUn m0 m' op e1 e λ m e' λ' m1 e1' λ1 σ = case op of
  ISZERO -> trivial
  EQLC _ -> trivial
  BoolToF -> trivial
  _ -> trivial

{-@ coherentBin :: m0:Nat -> m':Nat -> op:BinOp p -> e1:TypedDSL p -> e2:TypedDSL p
                -> e:{TypedDSL p | e = BIN op e1 e2}
                -> λ:LabelEnv p (Btwn 0 m0)

                -> m:{Nat | m0 <= m && m <= m'}
                -> e':LDSL p (Btwn 0 m)
                -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                -> m1:{Nat | m0 <= m1 && m1 <= m}
                -> e1':LDSL p (Btwn 0 m1)
                -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

                -> m2:{Nat | m1 <= m2 && m2 <= m}
                -> e2':LDSL p (Btwn 0 m2)
                -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                -> σ:{WireValuation p m' | closedExpr m' σ e'
                                        && coherentE m' e' σ}
                -> { closedExpr m' σ e1' && coherentE m' e1' σ &&
                     closedExpr m' σ e2' && coherentE m' e2' σ } @-}
coherentBin :: (Num p, Ord p)
            => Int -> Int -> BinOp p -> DSL p -> DSL p -> DSL p -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> WireValuation p -> Proof
coherentBin m0 m' op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 σ = case op of
  DIV -> trivial
  EQL -> trivial
  _ -> trivial

{-@ coherentCons :: m0:Nat -> m':Nat -> e1:TypedDSL p -> e2:TypedDSL p
                 -> e:{TypedDSL p | e = CONS e1 e2}
                 -> λ:LabelEnv p (Btwn 0 m0)

                 -> m:{Nat | m0 <= m && m <= m'}
                 -> e':LDSL p (Btwn 0 m)
                 -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                 -> m1:{Nat | m0 <= m1 && m1 <= m}
                 -> e1':LDSL p (Btwn 0 m1)
                 -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

                 -> m2:{Nat | m1 <= m2 && m2 <= m}
                 -> e2':LDSL p (Btwn 0 m2)
                 -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                 -> σ:{WireValuation p m' | closedExpr m' σ e'
                                         && coherentE m' e' σ}
                 -> { closedExpr m' σ e1' && coherentE m' e1' σ &&
                      closedExpr m' σ e2' && coherentE m' e2' σ } @-}
coherentCons :: (Num p, Ord p)
             => Int -> Int -> DSL p -> DSL p -> DSL p -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> WireValuation p -> Proof
coherentCons m0 m' e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 σ = trivial


{-@ tyEnvUn1 :: m0:Nat -> op:UnOp p -> e1:TypedDSL p
             -> e:{TypedDSL p | e = UN op e1}
             -> λ:LabelEnv p (Btwn 0 m0)

             -> m:{Nat | m0 <= m}
             -> e':LDSL p (Btwn 0 m)
             -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

             -> m1:{Nat | m0 <= m1 && m1 <= m}
             -> e1':LDSL p (Btwn 0 m1)
             -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

             -> γ:TyEnv' (Btwn 0 m0)
             -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnvE e' γ}

             -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ} @-}
tyEnvUn1 :: (Fractional p, Ord p) => Int -> UnOp p -> DSL p
           -> DSL p -> LabelEnv p Int

           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int

           -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvUn1 m0 op e1 e λ m e' λ' m1 e1' λ1 γ γ' =
  labelTyped e1 m0 λ  m1 e1' λ1 ??
  -- labelTyped e2 m1 λ1 m2 e2' λ2 ??
  case op of
    ISZERO -> case tyEnvE e1' γ of Just γ1 -> γ1
    EQLC _ -> case tyEnvE e1' γ of Just γ1 -> γ1
    BoolToF -> case tyEnvE e1' γ of Just γ1 -> γ1
    _   -> case tyEnvE e1' γ of Just γ1 -> γ1

{-@ tyEnvBin1 :: m0:Nat -> op:BinOp p -> e1:TypedDSL p -> e2:TypedDSL p
               -> e:{TypedDSL p | e = BIN op e1 e2}
               -> λ:LabelEnv p (Btwn 0 m0)

               -> m:{Nat | m0 <= m}
               -> e':LDSL p (Btwn 0 m)
               -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

               -> m1:{Nat | m0 <= m1 && m1 <= m}
               -> e1':LDSL p (Btwn 0 m1)
               -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

               -> m2:{Nat | m1 <= m2 && m2 <= m}
               -> e2':LDSL p (Btwn 0 m2)
               -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

               -> γ:TyEnv' (Btwn 0 m0)
               -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnvE e' γ}

               -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ} @-}
tyEnvBin1 :: (Fractional p, Ord p) => Int -> BinOp p -> DSL p -> DSL p
           -> DSL p -> LabelEnv p Int

           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int

           -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvBin1 m0 op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ' =
  labelTyped e1 m0 λ  m1 e1' λ1 ??
  -- labelTyped e2 m1 λ1 m2 e2' λ2 ??
  case op of
    DIV -> case tyEnvE e1' γ of Just γ1 -> γ1
    EQL -> case tyEnvE e1' γ of Just γ1 -> γ1
    _   -> case tyEnvE e1' γ of Just γ1 -> γ1

{-@ tyEnvBin2 :: m0:Nat -> op:BinOp p -> e1:TypedDSL p -> e2:TypedDSL p
               -> e:{TypedDSL p | e = BIN op e1 e2}
               -> λ:LabelEnv p (Btwn 0 m0)

               -> m:{Nat | m0 <= m}
               -> e':LDSL p (Btwn 0 m)
               -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

               -> m1:{Nat | m0 <= m1 && m1 <= m}
               -> e1':LDSL p (Btwn 0 m1)
               -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

               -> m2:{Nat | m1 <= m2 && m2 <= m}
               -> e2':LDSL p (Btwn 0 m2)
               -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

               -> γ:TyEnv' (Btwn 0 m0)
               -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnvE e' γ}
               -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ}

               -> γ2:{TyEnv' (Btwn 0 m2) | Just γ2 = tyEnvE e2' γ1} @-}
tyEnvBin2 :: (Fractional p, Ord p) => Int -> BinOp p -> DSL p -> DSL p
           -> DSL p -> LabelEnv p Int

           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int

           -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvBin2 m0 op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ' γ1 =
  labelTyped e1 m0 λ  m1 e1' λ1 ??
  labelTyped e2 m1 λ1 m2 e2' λ2 ??
  case op of
    DIV -> case tyEnvE e1' γ of
      Just γ1 -> case tyEnvE e2' γ1 of Just γ2 -> γ2
    EQL -> case tyEnvE e1' γ of
      Just γ1 -> case tyEnvE e2' γ1 of Just γ2 -> γ2
    _   -> case tyEnvE e1' γ of
      Just γ1 -> case tyEnvE e2' γ1 of Just γ2 -> γ2


{-@ tyEnvCons1 :: m0:Nat -> e1:TypedDSL p -> e2:TypedDSL p
               -> e:{TypedDSL p | e = CONS e1 e2}
               -> λ:LabelEnv p (Btwn 0 m0)

               -> m:{Nat | m0 <= m}
               -> e':LDSL p (Btwn 0 m)
               -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

               -> m1:{Nat | m0 <= m1 && m1 <= m}
               -> e1':LDSL p (Btwn 0 m1)
               -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

               -> m2:{Nat | m1 <= m2 && m2 <= m}
               -> e2':LDSL p (Btwn 0 m2)
               -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

               -> γ:TyEnv' (Btwn 0 m0)
               -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnvE e' γ}

               -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ} @-}
tyEnvCons1 :: (Fractional p, Ord p) => Int -> DSL p -> DSL p
           -> DSL p -> LabelEnv p Int

           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int

           -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvCons1 m0 e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ' =
  labelTyped e1 m0 λ  m1 e1' λ1 ??
  case tyEnvE e1' γ of Just γ1 -> γ1

{-@ tyEnvCons2 :: m0:Nat -> e1:TypedDSL p -> e2:TypedDSL p
               -> e:{TypedDSL p | e = CONS e1 e2}
               -> λ:LabelEnv p (Btwn 0 m0)

               -> m:{Nat | m0 <= m}
               -> e':LDSL p (Btwn 0 m)
               -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

               -> m1:{Nat | m0 <= m1 && m1 <= m}
               -> e1':LDSL p (Btwn 0 m1)
               -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

               -> m2:{Nat | m1 <= m2 && m2 <= m}
               -> e2':LDSL p (Btwn 0 m2)
               -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

               -> γ:TyEnv' (Btwn 0 m0)
               -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnvE e' γ}
               -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ}

               -> γ2:{TyEnv' (Btwn 0 m2) | Just γ2 = tyEnvE e2' γ1} @-}
tyEnvCons2 :: (Fractional p, Ord p) => Int -> DSL p -> DSL p
           -> DSL p -> LabelEnv p Int

           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int

           -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvCons2 m0 e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ' γ1 =
  labelTyped e1 m0 λ  m1 e1' λ1 ??
  labelTyped e2 m1 λ1 m2 e2' λ2 ??
  case tyEnvE e1' γ of
    Just γ1 -> case tyEnvE e2' γ1 of
      Just γ2 -> γ2


{-@ booleanUn1 :: m0:Nat -> m':Nat -> op:UnOp p -> e1:TypedDSL p
               -> e:{TypedDSL p | e = UN op e1}
               -> λ:LabelEnv p (Btwn 0 m0)

               -> m:{Nat | m0 <= m && m <= m'}
               -> e':LDSL p (Btwn 0 m)
               -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

               -> m1:{Nat | m0 <= m1 && m1 <= m}
               -> e1':LDSL p (Btwn 0 m1)
               -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

               -> γ:TyEnv' (Btwn 0 m0)
               -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ}
               -> γ':{TyEnv' (Btwn 0 m)  | Just γ' = tyEnvE e'  γ}

               -> σ:{WireValuation p m' | closedExpr m' σ e'}

               -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                               && M.lookup j γ' = Just TBool}
                     -> { boolean (M.lookup' j σ) } )

               -> ( j:{Btwn 0 m | S.member j (elemsSet λ1)
                               && M.lookup j γ1 = Just TBool}
                     -> { boolean (M.lookup' j σ) } ) @-}
booleanUn1 :: (Fractional p, Ord p) => Int -> Int -> UnOp p -> DSL p
           -> DSL p -> LabelEnv p Int

           -> Int -> LDSL p Int -> LabelEnv p Int
           -> Int -> LDSL p Int -> LabelEnv p Int

           -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int

           -> WireValuation p
           -> (Int -> Proof) -> (Int -> Proof)
booleanUn1 m0 m' op e1 e λ m e' λ' m1 e1' λ1 γ γ1 γ' σ h_bool j =
  labelTyped e m0 λ m e' λ' ?? case op of
    ISZERO -> case tyEnvE e1' γ of
                Just γ1 -> case insertIfCompatible w TF γ1 of
                  Just γw -> elementLemma j TBool γ1
                          -- ?? insertICIncr w TF γ2 γw j
                          -- ?? tyEnvEIncr e2' γ1 γ2 j
                          ?? insertICIncr w TF    γ1 γw j -- new
                          ?? insertICIncr i TBool γw γ' j -- new
                          ?? lookupLemma j γ1 ?? lookupLemma j γ'
                          -- ?? labelWFWire' e2 m1 λ1 m2 e2' λ2
                          ?? h_bool j
      where (w,i) = labelIs0 m0 e1 λ m1 e1' λ1 m e' λ'

    EQLC k -> case tyEnvE e1' γ of
                Just γ1 -> case insertIfCompatible w TF γ1 of
                  Just γw -> elementLemma j TBool γ1
                          -- ?? insertICIncr w TF γ2 γw j
                          -- ?? tyEnvEIncr e2' γ1 γ2 j
                          ?? insertICIncr w TF    γ1 γw j -- new
                          ?? insertICIncr i TBool γw γ' j -- new
                          ?? lookupLemma j γ1 ?? lookupLemma j γ'
                          -- ?? labelWFWire' e2 m1 λ1 m2 e2' λ2
                          ?? h_bool j
      where (w,i) = labelIsk m0 e1 λ k m1 e1' λ1 m e' λ'

    BoolToF -> h_bool j

    _   -> case tyEnvE e1' γ of
             Just γ1 -> case inferType' e' of
               Just τ -> elementLemma j TBool γ1
                      -- ?? tyEnvEIncr e2' γ1 γ2 j
                      ?? insertICIncr i τ γ1 γ' j -- new
                      ?? lookupLemma j γ1 ?? lookupLemma j γ'
                      -- ?? labelWFWire' e2 m1 λ1 m2 e2' λ2
                      ?? h_bool j
      where i = labelUn m0 e1 λ op m1 e1' λ1 m e' λ'


{-@ booleanBin1 :: m0:Nat -> m':Nat -> op:BinOp p -> e1:TypedDSL p -> e2:TypedDSL p
                -> e:{TypedDSL p | e = BIN op e1 e2}
                -> λ:LabelEnv p (Btwn 0 m0)

                -> m:{Nat | m0 <= m && m <= m'}
                -> e':LDSL p (Btwn 0 m)
                -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                -> m1:{Nat | m0 <= m1 && m1 <= m}
                -> e1':LDSL p (Btwn 0 m1)
                -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

                -> m2:{Nat | m1 <= m2 && m2 <= m}
                -> e2':LDSL p (Btwn 0 m2)
                -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                -> γ:TyEnv' (Btwn 0 m0)
                -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ}
                -> γ2:{TyEnv' (Btwn 0 m2) | Just γ2 = tyEnvE e2' γ1}
                -> γ':{TyEnv' (Btwn 0 m)  | Just γ' = tyEnvE e'  γ}

                -> σ:{WireValuation p m' | closedExpr m' σ e'}

                -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                                && M.lookup j γ' = Just TBool}
                      -> { boolean (M.lookup' j σ) } )

                -> ( j:{Btwn 0 m | S.member j (elemsSet λ1)
                                && M.lookup j γ1 = Just TBool}
                      -> { boolean (M.lookup' j σ) } ) @-}
booleanBin1 :: (Fractional p, Ord p) => Int -> Int -> BinOp p -> DSL p -> DSL p
            -> DSL p -> LabelEnv p Int

            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int

            -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int

            -> WireValuation p
            -> (Int -> Proof) -> (Int -> Proof)
booleanBin1 m0 m' op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ1 γ2 γ' σ h_bool j =
  labelTyped e m0 λ m e' λ' ?? case op of
    DIV -> case tyEnvE e1' γ of
             Just γ1 -> case tyEnvE e2' γ1 of
               Just γ2 -> case insertIfCompatible w TF γ2 of
                 Just γw -> elementLemma j TBool γ1
                         ?? insertICIncr w TF γ2 γw j
                         ?? tyEnvEIncr e2' γ1 γ2 j
                         ?? lookupLemma j γ1 ?? lookupLemma j γ2
                         ?? labelElems e2 m1 λ1 m2 e2' λ2
                         ?? h_2 j
      where (w,_) = labelDiv m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

    EQL -> case tyEnvE e1' γ of
             Just γ1 -> case tyEnvE e2' γ1 of
               Just γ2 -> case insertIfCompatible d TF γ2 of
                 Just γd -> case insertIfCompatible w TF γd of
                   Just γw -> elementLemma j TBool γ1
                           ?? insertICIncr d TF γ2 γd j
                           ?? insertICIncr w TF γd γw j
                           ?? tyEnvEIncr e2' γ1 γ2 j
                           ?? lookupLemma j γ1 ?? lookupLemma j γ2
                           ?? labelElems e2 m1 λ1 m2 e2' λ2
                           ?? h_2 j
      where (d,w,_) = labelEql m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

    _   -> case tyEnvE e1' γ of
             Just γ1 -> case tyEnvE e2' γ1 of
               Just γ2 -> elementLemma j TBool γ1
                       ?? tyEnvEIncr e2' γ1 γ2 j
                       ?? lookupLemma j γ1 ?? lookupLemma j γ2
                       ?? labelElems e2 m1 λ1 m2 e2' λ2
                       ?? h_2 j
  where h_2 = booleanBin2 m0 m' op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ1 γ2 γ' σ h_bool


{-@ booleanBin2 :: m0:Nat -> m':Nat -> op:BinOp p -> e1:TypedDSL p -> e2:TypedDSL p
                -> e:{TypedDSL p | e = BIN op e1 e2}
                -> λ:LabelEnv p (Btwn 0 m0)

                -> m:{Nat | m0 <= m && m <= m'}
                -> e':LDSL p (Btwn 0 m)
                -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                -> m1:{Nat | m0 <= m1 && m1 <= m}
                -> e1':LDSL p (Btwn 0 m1)
                -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

                -> m2:{Nat | m1 <= m2 && m2 <= m}
                -> e2':LDSL p (Btwn 0 m2)
                -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                -> γ:TyEnv' (Btwn 0 m0)
                -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ}
                -> γ2:{TyEnv' (Btwn 0 m2) | Just γ2 = tyEnvE e2' γ1}
                -> γ':{TyEnv' (Btwn 0 m)  | Just γ' = tyEnvE e'  γ}

                -> σ:{WireValuation p m' | closedExpr m' σ e'}

                -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                                && M.lookup j γ' = Just TBool}
                      -> { boolean (M.lookup' j σ) } )

                -> ( j:{Btwn 0 m | S.member j (elemsSet λ2)
                                && M.lookup j γ2 = Just TBool}
                      -> { boolean (M.lookup' j σ) } ) @-}
booleanBin2 :: (Fractional p, Ord p) => Int -> Int -> BinOp p -> DSL p -> DSL p
            -> DSL p -> LabelEnv p Int

            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int

            -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int

            -> WireValuation p
            -> (Int -> Proof) -> (Int -> Proof)
booleanBin2 m0 m' op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ1 γ2 γ' σ h_bool j =
  labelTyped e m0 λ m e' λ' ?? case op of
    DIV -> case tyEnvE e1' γ of
      Just γ1 -> case tyEnvE e2' γ1 of
        Just γ2 -> case insertIfCompatible w TF γ2 of
          Just γw -> elementLemma j TBool γ2
                  ?? insertICIncr w TF γ2 γw j
                  ?? insertICIncr i TF γw γ' j
                  ?? lookupLemma j γ2 ?? lookupLemma j γ'
                  ?? h_bool j
      where (w,i) = labelDiv m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

    EQL -> case tyEnvE e1' γ of
      Just γ1 -> case tyEnvE e2' γ1 of
        Just γ2 -> case insertIfCompatible d TF γ2 of
          Just γd -> case insertIfCompatible w TF γd of
            Just γw -> elementLemma j TBool γ2
                    ?? insertICIncr d TF    γ2 γd j
                    ?? insertICIncr w TF    γd γw j
                    ?? insertICIncr i TBool γw γ' j
                    ?? lookupLemma j γ2 ?? lookupLemma j γ'
                    ?? h_bool j
      where (d,w,i) = labelEql m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

    _ -> case tyEnvE e1' γ of
      Just γ1 -> case tyEnvE e2' γ1 of
        Just γ2 -> case inferType' e' of
          Just τ -> elementLemma j TBool γ2
                 ?? insertICIncr i τ γ2 γ' j
                 ?? lookupLemma j γ2 ?? lookupLemma j γ'
                 ?? h_bool j
      where i = labelBin m0 e1 e2 λ op m1 e1' λ1 m2 e2' λ2 m e' λ'

{-@ booleanCons1 :: m0:Nat -> m':Nat -> e1:TypedDSL p -> e2:TypedDSL p
                 -> e:{TypedDSL p | e = CONS e1 e2}
                 -> λ:LabelEnv p (Btwn 0 m0)

                 -> m:{Nat | m0 <= m && m <= m'}
                 -> e':LDSL p (Btwn 0 m)
                 -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                 -> m1:{Nat | m0 <= m1 && m1 <= m}
                 -> e1':LDSL p (Btwn 0 m1)
                 -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

                 -> m2:{Nat | m1 <= m2 && m2 <= m}
                 -> e2':LDSL p (Btwn 0 m2)
                 -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                 -> γ:TyEnv' (Btwn 0 m0)
                 -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ}
                 -> γ2:{TyEnv' (Btwn 0 m2) | Just γ2 = tyEnvE e2' γ1}
                 -> γ':{TyEnv' (Btwn 0 m)  | Just γ' = tyEnvE e'  γ}

                 -> σ:{WireValuation p m' | closedExpr m' σ e'}

                 -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                                 && M.lookup j γ' = Just TBool}
                       -> { boolean (M.lookup' j σ) } )

                 -> ( j:{Btwn 0 m | S.member j (elemsSet λ1)
                                 && M.lookup j γ1 = Just TBool}
                       -> { boolean (M.lookup' j σ) } ) @-}
booleanCons1 :: (Fractional p, Ord p) => Int -> Int -> DSL p -> DSL p
             -> DSL p -> LabelEnv p Int

             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int

             -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int

             -> WireValuation p
             -> (Int -> Proof) -> (Int -> Proof)
booleanCons1 m0 m' e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ1 γ2 γ' σ h_bool j =
  labelTyped e m0 λ m e' λ' ??
    case tyEnvE e1' γ of
      Just γ1 -> case tyEnvE e2' γ1 of
        Just γ2 -> elementLemma j TBool γ1
                ?? tyEnvEIncr e2' γ1 γ2 j
                ?? lookupLemma j γ1 ?? lookupLemma j γ2
                ?? labelElems e2 m1 λ1 m2 e2' λ2
                ?? h_bool j


{-@ booleanCons2 :: m0:Nat -> m':Nat -> e1:TypedDSL p -> e2:TypedDSL p
                 -> e:{TypedDSL p | e = CONS e1 e2}
                 -> λ:LabelEnv p (Btwn 0 m0)

                 -> m:{Nat | m0 <= m && m <= m'}
                 -> e':LDSL p (Btwn 0 m)
                 -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                 -> m1:{Nat | m0 <= m1 && m1 <= m}
                 -> e1':LDSL p (Btwn 0 m1)
                 -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ = (m1, e1', λ1)}

                 -> m2:{Nat | m1 <= m2 && m2 <= m}
                 -> e2':LDSL p (Btwn 0 m2)
                 -> λ2:{LabelEnv p (Btwn 0 m2) | label' e2 m1 λ1 = (m2, e2', λ2)}

                 -> γ:TyEnv' (Btwn 0 m0)
                 -> γ1:{TyEnv' (Btwn 0 m1) | Just γ1 = tyEnvE e1' γ}
                 -> γ2:{TyEnv' (Btwn 0 m2) | Just γ2 = tyEnvE e2' γ1}
                 -> γ':{TyEnv' (Btwn 0 m)  | Just γ' = tyEnvE e'  γ}

                 -> σ:{WireValuation p m' | closedExpr m' σ e'}

                 -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                                 && M.lookup j γ' = Just TBool}
                       -> { boolean (M.lookup' j σ) } )

                 -> ( j:{Btwn 0 m | S.member j (elemsSet λ2)
                                 && M.lookup j γ2 = Just TBool}
                       -> { boolean (M.lookup' j σ) } ) @-}
booleanCons2 :: (Fractional p, Ord p) => Int -> Int -> DSL p -> DSL p
             -> DSL p -> LabelEnv p Int

             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int
             -> Int -> LDSL p Int -> LabelEnv p Int

             -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int

             -> WireValuation p
             -> (Int -> Proof) -> (Int -> Proof)
booleanCons2 m0 m' e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ1 γ2 γ' σ h_bool j =
    labelTyped e m0 λ m e' λ' ??
    case tyEnvE e1' γ of
      Just γ1 -> case tyEnvE e2' γ1 of
        Just γ2 -> elementLemma j TBool γ2
                -- ?? tyEnvEIncr e2' γ1 γ2 j
                ?? lookupLemma j γ2 ?? lookupLemma j γ'
                -- ?? labelWFWire' e2 m1 λ1 m2 e2' λ2
                ?? h_bool j

-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
