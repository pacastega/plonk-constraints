{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--ple-with-undecided-guards" @-}
-- {-@ LIQUID "--fast" @-}
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



{-@ wiresUn :: m:Nat -> e1:LDSL p (Btwn 0 m)
            -> op:UnOp p -> i:Btwn 0 m
            -> e:{LDSL p (Btwn 0 m) | e = LUN op e1 i}
            -> { S.isSubsetOf (S.union (wiresE e1) (wWiresE e1))
                              (S.union (wiresE e)  (wWiresE e)) } @-}
wiresUn :: Int -> LDSL p Int -> UnOp p -> Int -> LDSL p Int -> Proof
wiresUn m e1 op i e = trivial

{-@ wiresBin1 :: m:Nat -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
              -> op:BinOp p -> i:Btwn 0 m
              -> e:{LDSL p (Btwn 0 m) | e = LBIN op e1 e2 i}
              -> { S.isSubsetOf (S.union (wiresE e1) (wWiresE e1))
                                (S.union (wiresE e)  (wWiresE e)) } @-}
wiresBin1 :: Int -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
          -> LDSL p Int -> Proof
wiresBin1 m e1 e2 op i e = trivial

{-@ wiresBin2 :: m:Nat -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
              -> op:BinOp p -> i:Btwn 0 m
              -> e:{LDSL p (Btwn 0 m) | e = LBIN op e1 e2 i}
              -> { S.isSubsetOf (S.union (wiresE e2) (wWiresE e2))
                                (S.union (wiresE e)  (wWiresE e)) } @-}
wiresBin2 :: Int -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
          -> LDSL p Int -> Proof
wiresBin2 m e1 e2 op i e = trivial


{-@ wiresCons1 :: m:Nat -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
               -> e:{LDSL p (Btwn 0 m) | e = LCONS e1 e2}
               -> { S.isSubsetOf (S.union (wiresE e1) (wWiresE e1))
                                 (S.union (wiresE e)  (wWiresE e)) } @-}
wiresCons1 :: Int -> LDSL p Int -> LDSL p Int -> LDSL p Int -> Proof
wiresCons1 m e1 i e = trivial

{-@ wiresCons2 :: m:Nat -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
               -> e:{LDSL p (Btwn 0 m) | e = LCONS e1 e2}
               -> { S.isSubsetOf (S.union (wiresE e2) (wWiresE e2))
                                 (S.union (wiresE e)  (wWiresE e)) } @-}
wiresCons2 :: Int -> LDSL p Int -> LDSL p Int -> LDSL p Int -> Proof
wiresCons2 m e1 i e = trivial


{-@ tyEnvUn :: m:Nat
            -> e1:LDSL p (Btwn 0 m) -> op:UnOp' p
            -> i:{Btwn 0 m | wellTyped' (LUN op e1 i)}
            -> τ:{Ty | inferType' (LUN op e1 i) = Just τ}
            -> γ:TyEnv' (Btwn 0 m)
            -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ (LUN op e1 i) γ}
            -> γ1:{TyEnv' (Btwn 0 m) | Just γ1 = tyEnv'_ e1 γ
                                    && Just γ' = insertIfCompatible i τ γ1} @-}
tyEnvUn :: Int -> LDSL p Int -> UnOp p -> Int -> Ty
        -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvUn m e1 op i τ γ γ' = case tyEnv'_ e1 γ of Just γ1 -> γ1

{-@ tyEnvBin1 :: m:Nat
              -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m) -> op:BinOp' p
              -> i:{Btwn 0 m | wellTyped' (LBIN op e1 e2 i)}
              -> γ:TyEnv' (Btwn 0 m)
              -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ (LBIN op e1 e2 i) γ}
              -> γ1:{TyEnv' (Btwn 0 m) | Just γ1 = tyEnv'_ e1 γ} @-}
tyEnvBin1 :: Int -> LDSL p Int -> LDSL p Int -> BinOp p -> Int
          -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvBin1 m e1 e2 op i γ γ' = case tyEnv'_ e1 γ of Just γ1 -> γ1

{-@ tyEnvBin2 :: m:Nat
              -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m) -> op:BinOp' p
              -> i:Btwn 0 m
              -> τ:{Ty | inferType' (LBIN op e1 e2 i) = Just τ}
              -> γ:TyEnv' (Btwn 0 m)
              -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ (LBIN op e1 e2 i) γ}
              -> γ1:{TyEnv' (Btwn 0 m) | Just γ1 = tyEnv'_ e1 γ}
              -> γ2:{TyEnv' (Btwn 0 m) | Just γ2 = tyEnv'_ e2 γ1
                                      && Just γ' = insertIfCompatible i τ γ2} @-}
tyEnvBin2 :: Int -> LDSL p Int -> LDSL p Int -> BinOp p -> Int -> Ty
          -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvBin2 m e1 e2 op i τ γ γ' γ1 = case tyEnv'_ e1 γ of
  Just γ1 -> case tyEnv'_ e2 γ1 of Just γ2 -> γ2

{-@ tyEnvCons1 :: m:Nat
               -> e1:LDSL p (Btwn 0 m) -> e2:{LDSL p (Btwn 0 m) | wellTyped' (LCONS e1 e2)}
               -> γ:TyEnv' (Btwn 0 m)
               -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ (LCONS e1 e2) γ}
               -> γ1:{TyEnv' (Btwn 0 m) | Just γ1 = tyEnv'_ e1 γ} @-}
tyEnvCons1 :: Int -> LDSL p Int -> LDSL p Int
           -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvCons1 m e1 e2 γ γ' = case tyEnv'_ e1 γ of Just γ1 -> γ1

{-@ tyEnvCons2 :: m:Nat
               -> e1:LDSL p (Btwn 0 m) -> e2:{LDSL p (Btwn 0 m) | wellTyped' (LCONS e1 e2)}
               -> γ:TyEnv' (Btwn 0 m)
               -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ (LCONS e1 e2) γ}
               -> γ1:{TyEnv' (Btwn 0 m) | Just γ1 = tyEnv'_ e1 γ}
               -> γ2:{TyEnv' (Btwn 0 m) | Just γ2 = tyEnv'_ e2 γ1
                                       && Just γ' = tyEnv'_ e2 γ1 } @-}
tyEnvCons2 :: Int -> LDSL p Int -> LDSL p Int
           -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int -> TyEnv' Int
tyEnvCons2 m e1 e2 γ γ' γ1 = case tyEnv'_ e1 γ of
  Just γ1 -> case tyEnv'_ e2 γ1 of Just γ2 -> γ2


{-@ typedScalarLUn :: m:Nat -> op:UnOp' p
                   -> e1:LDSL p (Btwn 0 m)
                   -> i:{Btwn 0 m | wellTyped' (LUN op e1 i)}
                   -> { scalar' (LUN op e1 i) } @-}
typedScalarLUn :: Int -> UnOp p -> LDSL p Int -> Int -> Proof
typedScalarLUn m op e1 i = case inferType' (LUN op e1 i) of
  Just (TVec _) -> error "impossible"
  Just _ -> trivial

{-@ typedScalarLBin :: m:Nat -> op:BinOp' p
                    -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
                    -> i:{Btwn 0 m | wellTyped' (LBIN op e1 e2 i)}
                    -> { scalar' (LBIN op e1 e2 i) } @-}
typedScalarLBin :: Int -> BinOp p -> LDSL p Int -> LDSL p Int -> Int -> Proof
typedScalarLBin m op e1 e2 i = case inferType' (LBIN op e1 e2 i) of
  Just (TVec _) -> error "impossible"
  Just _ -> trivial


{-@ labelEnvUn :: e1:DSL p -> op:{UnOp' p | wellTyped (UN op e1)}
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
  ISZERO -> error "not desugared"
  EQLC _ -> error "not desugared"
  BoolToF -> error "not desugared"
  _ -> trivial

{-@ labelEnvBin :: e1:DSL p -> e2:DSL p -> op:{BinOp' p | wellTyped (BIN op e1 e2)}
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
  DIV -> error "not desugared"
  EQL -> error "not desugared"
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


{-@ closedBin :: m:Nat -> σ:WireValuation p m -> op:BinOp' p
              -> e1:LDSL p (Btwn 0 m) -> e2:LDSL p (Btwn 0 m)
              -> i:{Btwn 0 m | wellTyped' (LBIN op e1 e2 i)
                            && closedExpr m σ (LBIN op e1 e2 i)}
              -> { M.member (outputWire e1) σ &&
                   M.member (outputWire e2) σ &&
                   M.member i σ } @-}
closedBin :: Int -> WireValuation p -> BinOp p -> LDSL p Int -> LDSL p Int
          -> Int -> Proof
closedBin m σ op e1 e2 i = trivial
  ? liquidAssert (S.member (outputWire e1) (wiresE e1 `S.union` wWiresE e1))
  ? liquidAssert (S.member (outputWire e2) (wiresE e2 `S.union` wWiresE e2))


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0
