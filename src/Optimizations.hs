module Optimizations (optimize) where

import Data.Maybe (fromMaybe)
import Control.Applicative ((<|>))
import Control.Monad ((>=>))

import DSL
import GlobalStore
import Utils (boolean)

type Opt p = DSL p -> Maybe (DSL p)

-- List of optimizations to apply
optimizations :: (Fractional p, Eq p) => [Opt p]
optimizations = [removeConstants ||| constantFolding]

-- Apply all optimizations
optimize :: (Fractional p, Eq p) =>
            GlobalStore p (DSL p) -> GlobalStore p (DSL p)
optimize = optimize' (foldr (>=>) pure optimizations) where
  optimize' f (GStore body store hints) =
    GStore (opt f body) (map (opt' f) store) hints

-- Try to apply optimization `f` at node `p`; if it fails, leave `p` unchanged
atNode :: Opt p -> DSL p -> DSL p
atNode f p = fromMaybe p (f p)

-- Combine two optimizations to apply them 'in parallel': if the first fails,
-- try the second one
(|||) :: Opt p -> Opt p -> Opt p
(|||) f1 f2 p = f1 p <|> f2 p

-- How to apply a general optimization on a program
opt :: Opt p -> DSL p -> DSL p
opt f p@VAR {}       = f `atNode` p
opt f p@(CONST {})   = f `atNode` p
opt f p@(BOOLEAN {}) = f `atNode` p

opt f p@(ADD p1 p2) = f `atNode` (ADD (opt f p1) (opt f p2))
opt f p@(SUB p1 p2) = f `atNode` (SUB (opt f p1) (opt f p2))
opt f p@(MUL p1 p2) = f `atNode` (MUL (opt f p1) (opt f p2))
opt f p@(DIV p1 p2) = f `atNode` (DIV (opt f p1) (opt f p2))

opt f p@(LINCOMB k1 p1 k2 p2) =
  f `atNode` (LINCOMB k1 (opt f p1) k2 (opt f p2))

opt f p@(NOT p1   ) = f `atNode` (NOT (opt f p1))
opt f p@(AND p1 p2) = f `atNode` (AND (opt f p1) (opt f p2))
opt f p@(OR  p1 p2) = f `atNode` (OR  (opt f p1) (opt f p2))
opt f p@(XOR p1 p2) = f `atNode` (XOR (opt f p1) (opt f p2))

opt f p@(UnsafeNOT p1   ) = f `atNode` (UnsafeNOT (opt f p1))
opt f p@(UnsafeAND p1 p2) = f `atNode` (UnsafeAND (opt f p1) (opt f p2))
opt f p@(UnsafeOR  p1 p2) = f `atNode` (UnsafeOR  (opt f p1) (opt f p2))
opt f p@(UnsafeXOR p1 p2) = f `atNode` (UnsafeXOR (opt f p1) (opt f p2))

opt f p@(ISZERO p1) = f `atNode` (ISZERO (opt f p1))
opt f p@(EQL p1 p2) = f `atNode` (EQL (opt f p1) (opt f p2))
opt f p@(EQLC p1 k) = f `atNode` (EQLC (opt f p1) k)

opt f p@(NIL _)     = f `atNode` p
opt f p@(CONS h ts) = f `atNode` (CONS (opt f h) (opt f ts))

-- How to apply a general optimization on an assertion
opt' :: Opt p -> Assertion p -> Assertion p
opt' f (DEF s p τ) = DEF s (opt f p) τ
opt' f (NZERO p) = NZERO (opt f p)
opt' f (BOOL p) = BOOL (opt f p)
opt' f (EQA p1 p2) = EQA (opt f p1) (opt f p2)

constantFolding :: (Fractional p, Eq p) => DSL p -> Maybe (DSL p)
constantFolding (ADD (CONST k1) (CONST k2)) = Just $ CONST (k1 + k2)
constantFolding (SUB (CONST k1) (CONST k2)) = Just $ CONST (k1 - k2)
constantFolding (MUL (CONST k1) (CONST k2)) = Just $ CONST (k1 * k2)
constantFolding (DIV (CONST k1) (CONST k2)) | k2 /= 0 = Just $ CONST (k1 / k2)

constantFolding (NOT (BOOLEAN b1)) = Just $ BOOLEAN (not b1)
constantFolding (AND (BOOLEAN b1) (BOOLEAN b2)) = Just $ BOOLEAN (b1 && b2)
constantFolding (OR  (BOOLEAN b1) (BOOLEAN b2)) = Just $ BOOLEAN (b1 || b2)
constantFolding (XOR (BOOLEAN b1) (BOOLEAN b2)) = Just $ BOOLEAN (b1 /= b2)

constantFolding (UnsafeNOT (BOOLEAN b1)) = Just $ BOOLEAN (not b1)
constantFolding (UnsafeAND (BOOLEAN b1) (BOOLEAN b2)) = Just $ BOOLEAN (b1 && b2)
constantFolding (UnsafeOR  (BOOLEAN b1) (BOOLEAN b2)) = Just $ BOOLEAN (b1 || b2)
constantFolding (UnsafeXOR (BOOLEAN b1) (BOOLEAN b2)) = Just $ BOOLEAN (b1 /= b2)

constantFolding (ISZERO (CONST k)) = Just $ BOOLEAN (k /= 0)
constantFolding (EQL (CONST k1) (CONST k2)) = Just $ BOOLEAN (k1 == k2)
constantFolding (EQLC (CONST k1) k2) = Just $ BOOLEAN (k1 == k2)

constantFolding _ = Nothing -- any other pattern is not a redex


removeConstants :: (Fractional p, Eq p) => DSL p -> Maybe (DSL p)
removeConstants (ADD (MUL (CONST k1) p1) (MUL (CONST k2) p2))
  = Just $ LINCOMB k1 p1 k2 p2
removeConstants (ADD (MUL p1 (CONST k1)) (MUL (CONST k2) p2))
  = Just $ LINCOMB k1 p1 k2 p2
removeConstants (ADD (MUL (CONST k1) p1) (MUL p2 (CONST k2)))
  = Just $ LINCOMB k1 p1 k2 p2
removeConstants (ADD (MUL p1 (CONST k1)) (MUL p2 (CONST k2)))
  = Just $ LINCOMB k1 p1 k2 p2
removeConstants (ADD (MUL (CONST k1) p1) p2)
  = Just $ LINCOMB k1 p1 1 p2
removeConstants (ADD (MUL p1 (CONST k1)) p2)
  = Just $ LINCOMB k1 p1 1 p2
removeConstants (ADD p1 (MUL (CONST k2) p2))
  = Just $ LINCOMB 1 p1 k2 p2
removeConstants (ADD p1 (MUL p2 (CONST k2)))
  = Just $ LINCOMB 1 p1 k2 p2
-- adding 0 is a no-op
removeConstants (ADD (CONST 0) p) = Just p
removeConstants (ADD p (CONST 0)) = Just p
-- subtracting 0 is a no-op
removeConstants (SUB p (CONST 0)) = Just p
-- multiplying by 1 is a no-op
removeConstants (MUL (CONST 1) p) = Just p
removeConstants (MUL p (CONST 1)) = Just p
-- multiplying by 0 always returns 0
removeConstants (MUL (CONST 0) p) = Just (CONST 0)
removeConstants (MUL p (CONST 0)) = Just (CONST 0)
-- dividing by 1 is a no-op
removeConstants (DIV p (CONST 1)) = Just p

removeConstants _ = Nothing -- any other pattern is not a redex
