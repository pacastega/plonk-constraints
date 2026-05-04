{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module WitnessGenProof.SemanticsLemmas where

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
import WitnessGeneration
import Semantics
import MapLemmas
import Language.Haskell.Liquid.ProofCombinators

-- sigmaVar ignores its first argument -----------------------------------------

{-@ sigmaVarLemma :: m:Nat -> m':{Nat | m' >= m}
                  -> e':LDSL p (Btwn 0 m) -> σ:WireValuation p m
                  -> { sigmaVar m e' σ = sigmaVar m' e' σ } @-}
sigmaVarLemma :: Int -> Int -> LDSL p Int -> WireValuation p -> Proof
sigmaVarLemma m m' e' σ = case e' of
  LNIL _ -> trivial
  LCONS e1' e2' -> sigmaVarLemma m m' e1' σ ? sigmaVarLemma m m' e2' σ
  _ -> trivial


{-@ sigmaVarIncr :: m:Nat -> e:TypedLDSL p (Btwn 0 m)
                 -> σ:{WireValuation p m | closedExpr m σ e}
                 -> σ':WireValuation p m
                 -> MapGE σ' σ
                 -> { sigmaVar m e σ = sigmaVar m e σ' } @-}
sigmaVarIncr :: Int -> LDSL p Int -> WireValuation p -> WireValuation p
             -> (Int -> Proof)
             -> Proof
sigmaVarIncr m e σ σ' π = case e of
  LNIL _ -> trivial
  LCONS e1 e2 -> sigmaVarIncr m e1 σ σ' π ? sigmaVarIncr m e2 σ σ' π
  _ -> case inferType' e of
    Just (TVec _) -> trivial
    Just _        -> π (outputWire e)


-- evaluating scalars only produces "VF" values --------------------------------

{-@ evalScalar :: e:ScalarDSL p -> ρ:NameValuation p
               -> v:{DSLValue p | eval e ρ = Just v}
               -> {x:p | v = VF x} @-}
evalScalar :: (Fractional p, Eq p) => DSL p -> NameValuation p -> DSLValue p -> p
evalScalar e ρ v = case inferType e of
  Just _ -> case eval e ρ of Just (VF x) -> x

{-@ sigmaVarScalar :: m:Nat -> e':ScalarLDSL p (Btwn 0 m)
                   -> σ:{WireValuation p m | closedExpr m σ e'}
                   -> { sigmaVar m e' σ = VF (M.lookup' (outputWire e') σ) } @-}
sigmaVarScalar :: Int -> LDSL p Int -> WireValuation p -> Proof
sigmaVarScalar m e' σ = case e' of
  LNIL _ -> error "e' is scalar"
  LCONS _ _ -> error "e' is scalar"
  _ -> trivial


-- eval works inductively on subexpressions ------------------------------------

{-@ evalDiv1 :: e1:DSL p -> e2:{DSL p | wellTyped (BIN DIV e1 e2)}
             -> ρ:NameValuation p
             -> v:{DSLValue p | eval (BIN DIV e1 e2) ρ = Just v}
             -> {v1:p | eval e1 ρ = Just (VF v1)} @-}
evalDiv1 :: (Fractional p, Eq p) => DSL p -> DSL p
         -> NameValuation p -> DSLValue p -> p
evalDiv1 e1 e2 ρ v = case eval e1 ρ of Just (VF v1) -> v1

{-@ evalDiv2 :: e1:DSL p -> e2:{DSL p | wellTyped (BIN DIV e1 e2)}
             -> ρ:NameValuation p
             -> v:{DSLValue p | eval (BIN DIV e1 e2) ρ = Just v}
             -> {v2:p | eval e2 ρ = Just (VF v2) && v2 /= 0} @-}
evalDiv2 :: (Fractional p, Eq p) => DSL p -> DSL p
         -> NameValuation p -> DSLValue p -> p
evalDiv2 e1 e2 ρ v = case eval e2 ρ of Just (VF v2) -> v2


{-@ evalUn :: e1:DSL p -> op:{UnOp' p | wellTyped (UN op e1)}
           -> ρ:NameValuation p
           -> v:{DSLValue p | eval (UN op e1) ρ = Just v}
           -> {v1:p | eval e1 ρ = Just (VF v1)} @-}
evalUn :: (Fractional p, Eq p) => DSL p -> UnOp p
       -> NameValuation p -> DSLValue p -> p
evalUn e1 op ρ v = case eval e1 ρ of Just (VF v1) -> v1

{-@ evalBin1 :: e1:DSL p -> e2:DSL p -> op:{BinOp' p | wellTyped (BIN op e1 e2)}
             -> ρ:NameValuation p
             -> v:{DSLValue p | eval (BIN op e1 e2) ρ = Just v}
             -> {v1:p | eval e1 ρ = Just (VF v1)} @-}
evalBin1 :: (Fractional p, Eq p) => DSL p -> DSL p -> BinOp p
         -> NameValuation p -> DSLValue p -> p
evalBin1 e1 e2 op ρ v = case eval e1 ρ of Just (VF v1) -> v1

{-@ evalBin2 :: e1:DSL p -> e2:DSL p -> op:{BinOp' p | wellTyped (BIN op e1 e2)}
             -> ρ:NameValuation p
             -> v:{DSLValue p | eval (BIN op e1 e2) ρ = Just v}
             -> {v2:p | eval e2 ρ = Just (VF v2)} @-}
evalBin2 :: (Fractional p, Eq p) => DSL p -> DSL p -> BinOp p
         -> NameValuation p -> DSLValue p -> p
evalBin2 e1 e2 op ρ v = case eval e2 ρ of Just (VF v2) -> v2


{-@ evalCons1 :: e1:DSL p -> e2:{DSL p | wellTyped (CONS e1 e2)}
              -> ρ:NameValuation p
              -> v:{DSLValue p | eval (CONS e1 e2) ρ = Just v}
              -> {v1:DSLValue p | eval e1 ρ = Just v1} @-}
evalCons1 :: (Fractional p, Eq p) => DSL p -> DSL p
          -> NameValuation p -> DSLValue p -> DSLValue p
evalCons1 e1 e2 ρ v = case eval e1 ρ of Just v1 -> v1

{-@ evalCons2 :: e1:DSL p -> e2:{DSL p | wellTyped (CONS e1 e2)}
              -> ρ:NameValuation p
              -> v:{DSLValue p | eval (CONS e1 e2) ρ = Just v}
              -> {v2:DSLValue p | eval e2 ρ = Just v2} @-}
evalCons2 :: (Fractional p, Eq p) => DSL p -> DSL p
          -> NameValuation p -> DSLValue p -> DSLValue p
evalCons2 e1 e2 ρ v = case eval e2 ρ of Just v2 -> v2


-- relation between eval of expression and its parts ---------------------------

{-@ evalVar :: s:Var -> τ:ScalarTy -> ρ:NameValuation p
            -> v:{p | eval (VAR s τ) ρ = Just (VF v)}
            -> { Just v = M.lookup s ρ } @-}
evalVar :: (Fractional p, Eq p) => Var -> Ty -> NameValuation p -> p -> Proof
evalVar s τ ρ v = case M.lookup s ρ of
  Just _ -> trivial


{-@ evalBinOp :: e1:DSL p -> e2:DSL p -> op:{BinOp' p | wellTyped (BIN op e1 e2)}
              -> ρ:NameValuation p
              -> v:{p | eval (BIN op e1 e2) ρ = Just (VF v)}
              -> {v1:p | eval e1 ρ = Just (VF v1)}
              -> {v2:p | eval e2 ρ = Just (VF v2)}
              -> { v = valueBinOp op v1 v2 } @-}
evalBinOp :: (Fractional p, Eq p) => DSL p -> DSL p -> BinOp p
          -> NameValuation p -> p -> p -> p -> Proof
evalBinOp e1 e2 op ρ v v1 v2 = case (eval e1 ρ, eval e2 ρ) of
  (Just (VF v1), Just (VF v2)) -> case op of
    DIV -> error "not desugared"
    EQL -> error "not desugared"
    _ -> trivial

{-@ evalUnOp :: e1:DSL p -> op:{UnOp' p | wellTyped (UN op e1)}
             -> ρ:NameValuation p
             -> v:{p | eval (UN op e1) ρ = Just (VF v)}
             -> {v1:p | eval e1 ρ = Just (VF v1)}
             -> { v = valueUnOp op v1 } @-}
evalUnOp :: (Fractional p, Eq p) => DSL p -> UnOp p
         -> NameValuation p -> p -> p -> Proof
evalUnOp e1 op ρ v v1 = case eval e1 ρ of
  Just (VF v1) -> case op of
    ISZERO -> error "not desugared"
    EQLC k -> error "not desugared"
    BoolToF -> error "not desugared"
    _ -> trivial
