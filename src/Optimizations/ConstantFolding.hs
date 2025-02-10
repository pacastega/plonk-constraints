{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Optimizations.ConstantFolding (constantFolding) where

import Optimizations.Base
import DSL

import Utils (any')

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect constantFolding @-}
{-@ constantFolding :: Opt p @-}
constantFolding :: (Fractional p, Eq p) => DSL p -> Maybe (DSL p)
constantFolding (ADD (CONST k1) (CONST k2)) = Just (CONST (k1 + k2))
constantFolding (SUB (CONST k1) (CONST k2)) = Just (CONST (k1 - k2))
constantFolding (MUL (CONST k1) (CONST k2)) = Just (CONST (k1 * k2))
constantFolding (DIV (CONST k1) (CONST k2)) | k2 /= 0 = Just (CONST (k1 / k2))

constantFolding (NOT (BOOLEAN b1)) = Just (BOOLEAN (not b1))
constantFolding (AND (BOOLEAN b1) (BOOLEAN b2)) = Just (BOOLEAN (b1 && b2))
constantFolding (OR  (BOOLEAN b1) (BOOLEAN b2)) = Just (BOOLEAN (b1 || b2))
constantFolding (XOR (BOOLEAN b1) (BOOLEAN b2)) = Just (BOOLEAN (b1 /= b2))

constantFolding (UnsafeNOT (BOOLEAN b1)) = Just (BOOLEAN (not b1))
constantFolding (UnsafeAND (BOOLEAN b1) (BOOLEAN b2)) = Just (BOOLEAN (b1 && b2))
constantFolding (UnsafeOR  (BOOLEAN b1) (BOOLEAN b2)) = Just (BOOLEAN (b1 || b2))
constantFolding (UnsafeXOR (BOOLEAN b1) (BOOLEAN b2)) = Just (BOOLEAN (b1 /= b2))

constantFolding (ISZERO (CONST k)) = Just (BOOLEAN (k == 0))
constantFolding (EQL (CONST k1) (CONST k2)) = Just (BOOLEAN (k1 == k2))
constantFolding (EQLC (CONST k1) k2) = Just (BOOLEAN (k1 == k2))

constantFolding _ = Nothing -- any other pattern is not a redex


{-@ constantFoldingProof :: v:ValuationRefl p
         -> d1:{TypedDSL p | scalar d1}
         -> d2:{TypedDSL p | scalar d2 && constantFolding d1 = Just d2}
         -> { eval d1 v = eval d2 v } @-}
constantFoldingProof :: (Fractional p, Eq p)
                     => ValuationRefl p -> DSL p -> DSL p -> Proof
constantFoldingProof _ d1 _ = case d1 of
  ADD _ _ -> trivial
  SUB _ _ -> trivial
  MUL _ _ -> trivial
  DIV _ _ -> trivial

  NOT _   -> trivial
  AND _ _ -> trivial
  OR  _ _ -> trivial
  XOR _ _ -> trivial

  UnsafeNOT _   -> trivial
  UnsafeAND _ _ -> trivial
  UnsafeOR  _ _ -> trivial
  UnsafeXOR _ _ -> trivial

  ISZERO _ -> trivial
  EQL  _ _ -> trivial
  EQLC _ _ -> trivial

  _ -> trivial
