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

{-@ constantFoldingProof :: ρ:NameValuation p
         -> d1:TypedDSL p
         -> d2:{TypedDSL p | constantFolding d1 = Just d2}
         -> { eval d1 ρ = eval d2 ρ } @-}
constantFoldingProof :: (Fractional p, Eq p)
                     => NameValuation p -> DSL p -> DSL p -> Proof
constantFoldingProof _ d1 _ = case d1 of
  ADD _ _ -> trivial
  SUB _ _ -> trivial
  MUL _ _ -> trivial
  DIV _ _ -> trivial

  NOT (BOOLEAN b) -> case b of True -> (); False -> ()
  AND (BOOLEAN b) (BOOLEAN c) -> case (b,c) of
    (False,False) -> trivial; (False,True) -> trivial;
    (True, False) -> trivial; (True, True) -> trivial;
  OR  (BOOLEAN b) (BOOLEAN c) -> case (b,c) of
    (False,False) -> trivial; (False,True) -> trivial;
    (True, False) -> trivial; (True, True) -> trivial;
  XOR (BOOLEAN b) (BOOLEAN c) -> case (b,c) of
    (False,False) -> trivial; (False,True) -> trivial;
    (True, False) -> trivial; (True, True) -> trivial;

  UnsafeNOT (BOOLEAN b) -> case b of True -> (); False -> ()
  UnsafeAND (BOOLEAN b) (BOOLEAN c) -> case (b,c) of
    (False,False) -> trivial; (False,True) -> trivial;
    (True, False) -> trivial; (True, True) -> trivial;
  UnsafeOR  (BOOLEAN b) (BOOLEAN c) -> case (b,c) of
    (False,False) -> trivial; (False,True) -> trivial;
    (True, False) -> trivial; (True, True) -> trivial;
  UnsafeXOR (BOOLEAN b) (BOOLEAN c) -> case (b,c) of
    (False,False) -> trivial; (False,True) -> trivial;
    (True, False) -> trivial; (True, True) -> trivial;

  ISZERO (CONST k1)            -> if k1 == 0  then trivial else trivial
  EQL    (CONST k1) (CONST k2) -> if k1 == k2 then trivial else trivial
  EQLC   (CONST k1) k2         -> if k1 == k2 then trivial else trivial
