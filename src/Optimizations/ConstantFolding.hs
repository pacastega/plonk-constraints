{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Optimizations.ConstantFolding (constantFolding) where

import Optimizations.Base
import DSL
import Semantics

import Utils (any', liftA2', fmap')

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect constantFolding @-}
{-@ constantFolding :: Opt p @-}
constantFolding :: (Fractional p, Eq p) => DSL p -> Maybe (DSL p)
constantFolding (BIN op (CONST k1) (CONST k2)) = case op of
  ADD -> Just (CONST (k1 + k2))
  SUB -> Just (CONST (k1 - k2))
  MUL -> Just (CONST (k1 * k2))
  DIV -> if k2 /= 0 then Just (CONST (k1 / k2)) else Nothing
  LINCOMB c1 c2 -> Just (CONST (c1*k1 + c2*k2))
  EQL -> Just (BOOLEAN (k1 == k2))
  _ -> Nothing

constantFolding (BIN op (BOOLEAN b1) (BOOLEAN b2)) = case op of
  AND -> Just (BOOLEAN (b1 && b2)); UnsafeAND -> Just (BOOLEAN (b1 && b2))
  OR  -> Just (BOOLEAN (b1 || b2)); UnsafeOR  -> Just (BOOLEAN (b1 || b2))
  XOR -> Just (BOOLEAN (b1 /= b2)); UnsafeXOR -> Just (BOOLEAN (b1 /= b2))
  _ -> Nothing

constantFolding (UN op (BOOLEAN b)) = case op of
  NOT -> Just (BOOLEAN (not b)); UnsafeNOT -> Just (BOOLEAN (not b))
  BoolToF -> if b then Just (CONST 1) else Just (CONST 0)
  _ -> Nothing

constantFolding (UN op (CONST k)) = case op of
  ADDC k' -> Just (CONST (k + k'))
  MULC k' -> Just (CONST (k * k'))
  ISZERO  -> Just (BOOLEAN (k == 0))
  EQLC k' -> Just (BOOLEAN (k == k'))
  _ -> Nothing

constantFolding _ = Nothing -- any other pattern is not a redex

{-@ constantFoldingProof :: ρ:NameValuation p
         -> d1:TypedDSL p
         -> d2:{TypedDSL p | constantFolding d1 = Just d2}
         -> { eval d1 ρ = eval d2 ρ } @-}
constantFoldingProof :: (Fractional p, Eq p)
                     => NameValuation p -> DSL p -> DSL p -> Proof
constantFoldingProof _ (BIN op (CONST _) (CONST _)) _ = case op of
  ADD -> trivial
  SUB -> trivial
  MUL -> trivial
  DIV -> trivial
  LINCOMB _ _ -> trivial
  EQL -> trivial

constantFoldingProof _ (BIN op (BOOLEAN _) (BOOLEAN _)) _ = case op of
  AND -> (); UnsafeAND -> ()
  OR  -> (); UnsafeOR  -> ()
  XOR -> (); UnsafeXOR -> ()

constantFoldingProof _ (UN op (BOOLEAN _)) _ = case op of
  NOT -> (); UnsafeNOT -> ()
  BoolToF -> ()

constantFoldingProof _ (UN op (CONST _)) _ = case op of
  ADDC _ -> ()
  MULC _ -> ()
  ISZERO -> ()
  EQLC _ -> ()
