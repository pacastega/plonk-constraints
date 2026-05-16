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
import WitnessGenProof.UniquenessOps
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

          -> γ:TyEnv' (Btwn 0 m0)
          -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ e' γ}
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
auxUn m0 m' op e1 e ρ λ m e' λ' τ σ π v γ γ' h_boolean = ()
  ?? m_gt_m1 -- m ≥ m1
  ?? wf1
  ?? uniqueUn m0 m' op e1 e ρ λ m1 e1' λ1 m e' λ' σ (v1 ? ih1) v

  where (m1,e1',λ1) = label' e1 m0 λ
        v1 = m_gt_m1
          ?? labelTyped e1 m0 λ m1 e1' λ1
          ?? wires1
          ?? evalWire m' e1' σ

        m_gt_m1 = labelIncUn op e1 m0 λ m1 e1' λ1 m e' λ'

        γ1 = tyEnvUn1 m0 op e1 e λ m e' λ' m1 e1' λ1 γ γ'
        h1 = booleanUn1 m0 m' op e1 e λ m e' λ' m1 e1' λ1 γ γ1 γ' σ h_boolean
        wf1 = labelWF e1 m0 λ  m1 e1' λ1 -- e1' is well-formed
        λ'_λ1 = labelEnvUn e1 op m0 λ m1 e1' λ1 m e' λ'
        wires1 = wiresUn e1 op m0 λ m1 e1' λ1 m e' λ'
        coherent1 = coherentUn m0 m' op e1 e λ m e' λ' m1 e1' λ1 σ

        {-@ π1 :: Agree λ' ρ σ @-}
        π1 :: String -> Proof
        π1 x = λ'_λ1 ?? π x

        ih1 = sizeUn e1 op
           ?? wf1
           ?? coherent1
           ?? evalWireUnique m0 m' e1 ρ λ m1 e1' λ1 σ π1 v1 γ  γ1 h1


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

           -> γ:TyEnv' (Btwn 0 m0)
           -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ e' γ}
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
auxBin m0 m' op e1 e2 e ρ λ m e' λ' τ σ π v γ γ' h_boolean = ()
        ?? m_gt_m1_m2 -- m ≥ m2 ≥ m1
        ?? wf1 ?? wf2
        ?? uniqueBin m0 m' op e1 e2 e ρ λ m1 e1' λ1 m2 e2' λ2 m e' λ' σ (v1 ? ih1) (v2 ? ih2) v

  where (m1,e1',λ1) = label' e1 m0 λ
        (m2,e2',λ2) = label' e2 m1 λ1
        v1 = m_gt_m1_m2
          ?? labelTyped e1 m0 λ  m1 e1' λ1
          ?? wires12
          ?? evalWire m' e1' σ
        v2 = m_gt_m1_m2
          ?? labelTyped e2 m1 λ1 m2 e2' λ2
          ?? wires12
          ?? evalWire m' e2' σ

        m_gt_m1_m2 = labelIncBin op e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

        γ1 = tyEnvBin1 m0 op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ'
        γ2 = tyEnvBin2 m0 op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ' γ1

        h1 = booleanBin1 m0 m' op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ1 γ2 γ' σ h_boolean
        h2 = booleanBin2 m0 m' op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ1 γ2 γ' σ h_boolean

        wf1 = labelWF e1 m0 λ  m1 e1' λ1 -- e1' is well-formed
        wf2 = labelWF e2 m1 λ1 m2 e2' λ2 -- e2' is well-formed

        λ'_λ2 = labelEnvBin e1 e2 op m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

        wires12 = wiresBin e1 e2 op m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

        coherent12 = coherentBin m0 m' op e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 σ

        {-@ π1 :: Agree λ1 ρ σ @-}
        π1 :: String -> Proof
        π1 x = labelIncrEnv e2 m1 λ1 m2 e2' λ2 x
            ?? λ'_λ2 ?? π2 x

        {-@ π2 :: Agree λ' ρ σ @-}
        π2 :: String -> Proof
        π2 x = π x

        ih1 = sizeBin e1 e2 op
           ?? wf1
           ?? coherent12
           ?? evalWireUnique m0 m' e1 ρ λ m1 e1' λ1 σ π1 v1 γ  γ1 h1
        ih2 = sizeBin e1 e2 op
           ?? wf2
           ?? coherent12
           ?? evalWireUnique m1 m' e2 ρ λ1 m2 e2' λ2 σ π2 v2 γ1 γ2 h2


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

            -> γ:TyEnv' (Btwn 0 m0)
            -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ e' γ}
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
auxCons m0 m' e1 e2 e ρ λ m e' λ' τ σ π v γ γ' h_boolean = ()
        ?? m_gt_m1_m2 -- m ≥ m2 ≥ m1
        ?? wf1 ?? wf2
        ?? uniqueCons m0 m' e1 e2 e ρ λ m1 e1' λ1 m2 e2' λ2 m e' λ' σ (v1 ? ih1) (v2 ? ih2) v

  where (m1,e1',λ1) = label' e1 m0 λ
        (m2,e2',λ2) = label' e2 m1 λ1
        v1 = m_gt_m1_m2
          ?? labelTyped e1 m0 λ  m1 e1' λ1
          ?? wires12
          ?? evalWire m' e1' σ
        v2 = m_gt_m1_m2
          ?? labelTyped e2 m1 λ1 m2 e2' λ2
          ?? wires12
          ?? evalWire m' e2' σ

        m_gt_m1_m2 = labelIncCons e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

        γ1 = tyEnvCons1 m0 e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ'
        γ2 = tyEnvCons2 m0 e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ' γ1

        h1 = booleanCons1 m0 m' e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ1 γ2 γ' σ h_boolean
        h2 = booleanCons2 m0 m' e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 γ γ1 γ2 γ' σ h_boolean

        wf1 = labelWF e1 m0 λ  m1 e1' λ1 -- e1' is well-formed
        wf2 = labelWF e2 m1 λ1 m2 e2' λ2 -- e2' is well-formed

        λ'_λ2 = labelEnvCons e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

        wires12 = wiresCons e1 e2 m0 λ m1 e1' λ1 m2 e2' λ2 m e' λ'

        coherent12 = coherentCons m0 m' e1 e2 e λ m e' λ' m1 e1' λ1 m2 e2' λ2 σ

        {-@ π1 :: Agree λ1 ρ σ @-}
        π1 :: String -> Proof
        π1 x = labelIncrEnv e2 m1 λ1 m2 e2' λ2 x
            ?? λ'_λ2 ?? π2 x

        {-@ π2 :: Agree λ' ρ σ @-}
        π2 :: String -> Proof
        π2 x = π x

        ih1 = sizeCons e1 e2
           ?? wf1
           ?? coherent12
           ?? evalWireUnique m0 m' e1 ρ λ m1 e1' λ1 σ π1 v1 γ  γ1 h1
        ih2 = sizeCons e1 e2
           ?? wf2
           ?? coherent12
           ?? evalWireUnique m1 m' e2 ρ λ1 m2 e2' λ2 σ π2 v2 γ1 γ2 h2


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

                   -> γ:TyEnv' (Btwn 0 m0)
                   -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnv'_ e' γ}
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
