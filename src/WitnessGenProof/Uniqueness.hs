{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--linear" @-}
module WitnessGenProof.Uniqueness where

import Constraints
import TypeAliases
import DSL
import Semantics
import Label
import WitnessGeneration

import Utils

import BooleanProof

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import MapLemmas
import LabelingProof.LabelingLemmas
import LabelingProof.RecursiveLemmas
import WitnessGenProof.WitnessGenLemmas
import WitnessGenProof.SemanticsLemmas
import WitnessGenProof.UniquenessLemmas

import WitnessGenProof.UniquenessBase
import WitnessGenProof.Uniqueness2 --FIXME: these lemmas should go somewhere else

import Language.Haskell.Liquid.ProofCombinators


{-@ auxUn :: m0:Nat -> m':Nat -> op:UnOp p -> e1:TypedDSL p
          -> e:{TypedDSL p | e = UN op e1}
          -> ρ:NameValuation p
          -> λ:LabelEnv p (Btwn 0 m0)

          -> m:{Nat | m0 <= m && m <= m'}
          -> e':{TypedLDSL p (Btwn 0 m) | wfE e'}
          -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

          -> τ:{Ty | inferType' e' = Just τ}

          -> {σ:WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
          -> Agree λ' ρ σ
          -> v:{DSLValue p | evalWire m' e' σ = v}

          -> γ:TyEnv' (Btwn 0 m')
          -> γ':{TyEnv' (Btwn 0 m') | Just γ' = tyEnv'_ e' γ}
          -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                          && M.lookup j γ' = Just TBool}
                 -> { boolean (M.lookup' j σ) } )

          -> { eval e ρ = Just v }
           / [size (UN op e1), 0] @-}
auxUn :: (Fractional p, Ord p) => Int -> Int -> UnOp p -> DSL p
      -> DSL p -> NameValuation p -> LabelEnv p Int

      -> Int -> LDSL p Int -> LabelEnv p Int -> Ty
      -> WireValuation p -> (String -> Proof) -> DSLValue p

      -> TyEnv' Int -> TyEnv' Int -> (Int -> Proof)
      -> Proof
auxUn m0 m' op e1 e ρ λ m e' λ' τ σ π v γ γ' h_boolean =
  sizeUn e1 op ??
  let (m1,e1',λ1) = label' e1 m0 λ
      m_gt_m1 = labelIncUn op e1 m0 λ m1 e1' λ1 m e' λ'
  in case op of
      ISZERO -> admit ()
      EQLC _ -> admit ()
      BoolToF -> admit ()
      _ -> m_gt_m1 -- m ≥ m1

        ?? coherentE m' e' σ -- σ ⊢ e1'

        ?? λ'_λ1 -- λ' == λ1

        ?? labelWF e1 m0 λ  m1 e1' λ1 -- e1' is well-formed
        ?? evalWireUnique m0 m' e1 ρ λ  m1 e1' λ1 σ π v1 γ  γ1 h_1 -- IH1: v1 = eval e1 ρ

        ?? scalarUn m' e1' op i -- e1' is scalar

        ?? evalWireScalar m' e1' σ -- v1 = evalWire m' e1' σ = Just (σ[outputWire e1'])

        ?? wires1 -- the wires of e1' are also wires of e'

        ?? typedScalarLUn m' op e1' i -- e' is scalar
        ?? evalWireScalar m' e' σ -- evalWire m' e' σ = Just (σ[i])
        ?? eval e ρ -- eval e ρ = Just (valueBinOp op v1 v2)

        ?? liquidAssert (i == outputWire e')

        where wires1 = wiresUn m' e1' op i (LUN op e1' i)

              v1 = m_gt_m1
                ?? labelTyped e1 m0 λ  m1 e1' λ1
                ?? wires1
                ?? evalWire m' e1' σ

              γ1 = tyEnvUn m' e1' op i τ γ γ'

              i = labelUn m0 e1 λ op m1 e1' λ1 m e' λ'

              {-@ h_1 :: j:{Btwn 0 m | S.member j (elemsSet λ1)
                                    && M.lookup j γ1 = Just TBool}
                      -> { boolean (M.lookup' j σ) } @-}
              h_1 :: Int -> Proof
              h_1 j = liquidAssert (Just γ' == insertIfCompatible i τ γ1)
                   ?? lookupInsertIC i τ γ1 γ' j
                   ?? λ'_λ1
                   ?? h_boolean j

              {-@ λ'_λ1 :: { λ' = λ1 } @-}
              λ'_λ1 = labelEnvUn e1 op m0 λ m1 e1' λ1 m e' λ'


{-@ auxBin :: m0:Nat -> m':Nat -> op:BinOp p -> e1:TypedDSL p -> e2:TypedDSL p
           -> e:{TypedDSL p | e = BIN op e1 e2}
           -> ρ:NameValuation p
           -> λ:LabelEnv p (Btwn 0 m0)

           -> m:{Nat | m0 <= m && m <= m'}
           -> e':{TypedLDSL p (Btwn 0 m) | wfE e'}
           -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

           -> τ:{Ty | inferType' e' = Just τ}

           -> {σ:WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
           -> Agree λ' ρ σ
           -> v:{DSLValue p | evalWire m' e' σ = v}

           -> γ:TyEnv' (Btwn 0 m')
           -> γ':{TyEnv' (Btwn 0 m') | Just γ' = tyEnv'_ e' γ}
           -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                           && M.lookup j γ' = Just TBool}
                  -> { boolean (M.lookup' j σ) } )

           -> { eval e ρ = Just v }
            / [size (BIN op e1 e2), 0] @-}
auxBin :: (Fractional p, Ord p) => Int -> Int -> BinOp p -> DSL p -> DSL p
       -> DSL p -> NameValuation p -> LabelEnv p Int

       -> Int -> LDSL p Int -> LabelEnv p Int -> Ty
       -> WireValuation p -> (String -> Proof) -> DSLValue p

       -> TyEnv' Int -> TyEnv' Int -> (Int -> Proof)
       -> Proof
auxBin m0 m' op e1 e2 e ρ λ m e' λ' τ σ π v γ γ' h_boolean =
  sizeBin e1 e2 op ?? case op of
      DIV -> admit ()
      EQL -> admit ()
      _ -> m_gt_m1_m2 -- m ≥ m2 ≥ m1

        ?? coherentE m' e' σ -- σ ⊢ e1', σ ⊢ e2'

        ?? labelWF e1 m0 λ  m1 e1' λ1 -- e1' is well-formed
        ?? evalWireUnique m0 m' e1 ρ λ  m1 e1' λ1 σ π1 v1 γ  γ1 h_1 -- IH1: v1 = eval e1 ρ

        ?? λ'_λ2 -- λ' == λ2

        ?? labelWF e2 m1 λ1 m2 e2' λ2 -- e2' is well-formed
        ?? evalWireUnique m1 m' e2 ρ λ1 m2 e2' λ2 σ π  v2 γ1 γ2 h_2 -- IH2: v2 = eval e2 ρ

        ?? scalarBin m' e1' e2' op i -- e1' and e2' are scalars

        ?? evalWireScalar m' e1' σ -- v1 = evalWire m' e1' σ = Just (σ[outputWire e1'])
        ?? evalWireScalar m' e2' σ -- v2 = evalWire m' e2' σ = Just (σ[outputWire e2'])

        ?? wires1 ?? wires2 -- the wires of e1', e2' are also wires of e'

        ?? typedScalarLBin m' op e1' e2' i -- e' is scalar
        ?? evalWireScalar m' e' σ -- evalWire m' e' σ = Just (σ[i])
        ?? eval e ρ -- eval e ρ = Just (valueBinOp op v1 v2)

        ?? liquidAssert (i == outputWire e')

        where (m1,e1',λ1) = label' e1 m0 λ
              (m2,e2',λ2) = label' e2 m1 λ1
              v1 = m_gt_m1_m2
                ?? labelTyped e1 m0 λ  m1 e1' λ1
                ?? wires1
                ?? evalWire m' e1' σ
              v2 = m_gt_m1_m2
                ?? labelTyped e2 m1 λ1 m2 e2' λ2
                ?? wires2
                ?? evalWire m' e2' σ

              wires1 = wiresBin1 m' e1' e2' op i (LBIN op e1' e2' i)
              wires2 = wiresBin2 m' e1' e2' op i (LBIN op e1' e2' i)

              γ1 = tyEnvBin1 m' e1' e2' op i   γ γ'
              γ2 = tyEnvBin2 m' e1' e2' op i τ γ γ' γ1

              m_gt_m1_m2 = labelIncBin op e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

              {-@ π1 :: Agree λ1 ρ σ @-}
              π1 :: String -> Proof
              π1 x = labelIncrEnv e2 m1 λ1 m2 e2' λ2 x
                  ?? λ'_λ2
                  ?? π x

              i = labelBin m0 e1 e2 λ op m1 e1' λ1 m2 e2' λ2 m e' λ'

              {-@ h_2 :: j:{Btwn 0 m | S.member j (elemsSet λ2)
                                    && M.lookup j γ2 = Just TBool}
                      -> { boolean (M.lookup' j σ) } @-}
              h_2 :: Int -> Proof
              h_2 j = liquidAssert (Just γ' == insertIfCompatible i τ γ2)
                   ?? lookupInsertIC i τ γ2 γ' j
                   ?? λ'_λ2
                   ?? h_boolean j

              {-@ h_1 :: j:{Btwn 0 m | S.member j (elemsSet λ1)
                                   && M.lookup j γ1 = Just TBool}
                      -> { boolean (M.lookup' j σ) } @-}
              h_1 :: Int -> Proof
              h_1 j = elementLemma j TBool γ1
                   ?? tyEnv'_incr e2' γ1 γ2 j
                   ?? lookupLemma j γ1 ?? lookupLemma j γ2
                   ?? labelWFWire' e2 m1 λ1 m2 e2' λ2
                   ?? h_2 j

              {-@ λ'_λ2 :: { λ' = λ2 }  @-}
              λ'_λ2 = labelEnvBin e1 e2 op m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'


{-@ auxCons :: m0:Nat -> m':Nat -> e1:TypedDSL p -> e2:TypedDSL p
            -> e:{TypedDSL p | e = CONS e1 e2}
            -> ρ:NameValuation p
            -> λ:LabelEnv p (Btwn 0 m0)

            -> m:{Nat | m0 <= m && m <= m'}
            -> e':{TypedLDSL p (Btwn 0 m) | wfE e'}
            -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

            -> τ:{Ty | inferType' e' = Just τ}

            -> {σ:WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
            -> Agree λ' ρ σ
            -> v:{DSLValue p | evalWire m' e' σ = v}

            -> γ:TyEnv' (Btwn 0 m')
            -> γ':{TyEnv' (Btwn 0 m') | Just γ' = tyEnv'_ e' γ}
            -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                            && M.lookup j γ' = Just TBool}
                   -> { boolean (M.lookup' j σ) } )

            -> { eval e ρ = Just v }
             / [size (CONS e1 e2), 0] @-}
auxCons :: (Fractional p, Ord p) => Int -> Int -> DSL p -> DSL p
        -> DSL p -> NameValuation p -> LabelEnv p Int

        -> Int -> LDSL p Int -> LabelEnv p Int -> Ty
        -> WireValuation p -> (String -> Proof) -> DSLValue p

        -> TyEnv' Int -> TyEnv' Int -> (Int -> Proof)
        -> Proof
auxCons m0 m' e1 e2 e ρ λ m e' λ' τ σ π v γ γ' h_boolean =
           sizeCons e1 e2
        ?? m_gt_m1_m2 -- m ≥ m2 ≥ m1
        ?? wires1 ?? wires2 -- the wires of e1', e2' are also wires of e'

        ?? coherentE m' e' σ -- σ ⊢ e1', σ ⊢ e2'

        ?? labelWF e1 m0 λ  m1 e1' λ1 -- e1' is well-formed
        ?? evalWireUnique m0 m' e1 ρ λ  m1 e1' λ1 σ π1 v1 γ  γ1 h_1 -- IH1: v1 = eval e1 ρ

        ?? λ'_λ2 -- λ' == λ2

        ?? labelWF e2 m1 λ1 m2 e2' λ2 -- e2' is well-formed
        ?? evalWireUnique m1 m' e2 ρ λ1 m2 e2' λ2 σ π  v2 γ1 γ2 h_2 -- IH2: v2 = eval e2 ρ

        ?? evalWire m' e' σ
        ?? eval e ρ -- eval e ρ = Just (valueBinOp op v1 v2)
        ?? trivial

        -- ?? liquidAssert (i == outputWire e')

        where (m1,e1',λ1) = label' e1 m0 λ
              (m2,e2',λ2) = label' e2 m1 λ1
              v1 = m_gt_m1_m2
                ?? labelTyped e1 m0 λ  m1 e1' λ1
                ?? wires1
                ?? liquidAssert (S.isSubsetOf (wiresE e1' `S.union` wWiresE e1')
                                              (wiresE e' `S.union` wWiresE e'))
                ?? liquidAssert (S.isSubsetOf (wiresE e' `S.union` wWiresE e')
                                              (M.keysSet σ))
                ?? evalWire m' e1' σ
              v2 = m_gt_m1_m2
                ?? labelTyped e2 m1 λ1 m2 e2' λ2
                ?? wires2
                ?? liquidAssert (S.isSubsetOf (wiresE e2' `S.union` wWiresE e2')
                                              (wiresE e' `S.union` wWiresE e'))
                ?? liquidAssert (S.isSubsetOf (wiresE e' `S.union` wWiresE e')
                                              (M.keysSet σ))
                ?? evalWire m' e2' σ

              wires1 = cons_thm ?? wiresCons1 m' e1' e2' (LCONS e1' e2')
              wires2 = cons_thm ?? wiresCons2 m' e1' e2' (LCONS e1' e2')

              γ1 = cons_thm ?? tyEnvCons1 m' e1' e2' γ γ'
              γ2 = cons_thm ?? tyEnvCons2 m' e1' e2' γ γ' γ1

              m_gt_m1_m2 = labelIncCons e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

              cons_thm = labelCons m0 e1 e2 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

              {-@ π1 :: Agree λ1 ρ σ @-}
              π1 :: String -> Proof
              π1 x = labelIncrEnv e2 m1 λ1 m2 e2' λ2 x
                  ?? λ'_λ2
                  ?? π x

              {-@ h_2 :: j:{Btwn 0 m | S.member j (elemsSet λ')
                                    && M.lookup j γ' = Just TBool}
                      -> { boolean (M.lookup' j σ) } @-}
              h_2 :: Int -> Proof
              h_2 j = ()
                      -- liquidAssert (Just γ' == insertIfCompatible i τ γ2)
                   -- ?? lookupInsertIC i τ γ2 γ' j
                   ?? λ'_λ2
                   ?? h_boolean j

              {-@ h_1 :: j:{Btwn 0 m | S.member j (elemsSet λ1)
                                   && M.lookup j γ1 = Just TBool}
                      -> { boolean (M.lookup' j σ) } @-}
              h_1 :: Int -> Proof
              h_1 j = elementLemma j TBool γ1
                   ?? tyEnv'_incr e2' γ1 γ2 j
                   ?? lookupLemma j γ1 ?? lookupLemma j γ'
                   ?? labelWFWire' e2 m1 λ1 m2 e2' λ2
                   ?? h_2 j

              {-@ λ'_λ2 :: { λ' = λ2 }  @-}
              λ'_λ2 = labelEnvCons e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'


{-@ evalWireUnique :: m0:Nat -> m':Nat
                   -> e:TypedDSL p
                   -> ρ:NameValuation p
                   -> λ:LabelEnv p (Btwn 0 m0)

                   -> m:{Nat | m0 <= m && m <= m'}
                   -> e':{TypedLDSL p (Btwn 0 m) | wfE e'}
                   -> λ':{LabelEnv p (Btwn 0 m) | label' e m0 λ = (m, e', λ')}

                   -> {σ:WireValuation p m' | closedExpr m' σ e' && coherentE m' e' σ}
                   -> Agree λ' ρ σ
                   -> v:{DSLValue p | evalWire m' e' σ = v}

                   -> γ:TyEnv' (Btwn 0 m')
                   -> γ':{TyEnv' (Btwn 0 m') | Just γ' = tyEnv'_ e' γ}
                   -> ( j:{Btwn 0 m | S.member j (elemsSet λ')
                                   && M.lookup j γ' = Just TBool}
                          -> { boolean (M.lookup' j σ) } )

                   -> { eval e ρ = Just v }
                    / [size e, 1] @-}
evalWireUnique :: (Fractional p, Ord p) => Int -> Int -> DSL p
               -> NameValuation p -> LabelEnv p Int

               -> Int -> LDSL p Int -> LabelEnv p Int
               -> WireValuation p -> (String -> Proof) -> DSLValue p

               -> TyEnv' Int -> TyEnv' Int -> (Int -> Proof)
               -> Proof
evalWireUnique m0 m' e ρ λ m e' λ' σ π v γ γ' h_boolean = case inferType' e' of
  Just τ -> case e of
    VAR s τ -> uniqueVar   m0 m' s τ e ρ λ m e' λ' σ π v γ γ' h_boolean
    CONST x -> uniqueConst m0 m' x   e ρ λ m e' λ' σ π v γ γ' h_boolean
    BOOL b  -> uniqueBool  m0 m' b   e ρ λ m e' λ' σ π v γ γ' h_boolean

    UN op e1 -> wellTypedUn e1 op
             ?? auxUn m0 m' op e1 e ρ λ m e' λ' τ σ π v γ γ' h_boolean

    BIN op e1 e2 -> wellTypedBin e1 e2 op
                 ?? auxBin m0 m' op e1 e2 e ρ λ m e' λ' τ σ π v γ γ' h_boolean

    NIL τ -> eval e ρ ?? evalWire m' e' σ ?? labelNil m0 τ λ m e' λ'
    CONS e1 e2 -> wellTypedCons e1 e2
               ?? auxCons m0 m' e1 e2 e ρ λ m e' λ' τ σ π v γ γ' h_boolean

  _ -> liquidAssert (wellTyped' e') ?? error "impossible"


{-@ assume admit :: () -> { False } @-}
admit :: () -> ()
admit _ = ()
