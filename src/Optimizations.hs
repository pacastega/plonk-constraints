{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--max-case-expand=0" @-}
module Optimizations (optimize) where

import Data.Maybe (fromMaybe)
import Control.Applicative ((<|>))
import Control.Monad ((>=>))

import DSL
import GlobalStore
import Utils (boolean, any', (??), foldr')

import Optimizations.ConstantFolding
import Optimizations.RemoveConstants
import Optimizations.Base

-- List of optimizations to apply
{-@ optimizations :: [Opt p] @-}
optimizations :: (Fractional p, Eq p) => [Opt p]
optimizations = [constantFolding ||| removeConstants]

-- Apply all optimizations
{-@ optimize :: GlobalStore p ({d:DSL p | wellTyped d})
             -> GlobalStore p ({d:DSL p | wellTyped d}) @-}
optimize :: (Fractional p, Eq p) =>
            GlobalStore p (DSL p) -> GlobalStore p (DSL p)
optimize program = optimize' (foldr' (>=>) pure optimizations) program where
  {-@ optimize' :: Opt p -> GlobalStore p ({d:DSL p | wellTyped d})
                -> GlobalStore p ({d:DSL p | wellTyped d}) @-}
  optimize' :: Opt p -> GlobalStore p (DSL p) -> GlobalStore p (DSL p)
  optimize' f (GStore body store hints) =
    GStore (opt f body) (map (opt' f) store) hints

-- Try to apply optimization `f` at node `p`; if it fails, leave `p` unchanged
{-@ atNode :: Opt p -> d:TypedDSL p -> {v:TypedDSL p | sameType v d} @-}
atNode :: Opt p -> DSL p -> DSL p
atNode f p = fromMaybe p (f p)

-- Combine two optimizations to apply them 'in parallel': if the first fails,
-- try the second one
{-@ (|||) :: Opt p -> Opt p -> Opt p @-}
(|||) :: Opt p -> Opt p -> Opt p
(|||) f1 f2 p = f1 p <|> f2 p

-- How to apply a general optimization on a program
{-@ opt :: Opt p -> d:TypedDSL p -> {v:TypedDSL p | sameType v d} @-}
opt :: Opt p -> DSL p -> DSL p
opt f p@VAR {}       = f `atNode` p
opt f p@(CONST {})   = f `atNode` p
opt f p@(BOOLEAN {}) = f `atNode` p
opt f p@(BIT {})     = f `atNode` p

opt f p@(ADD p1 p2) = f `atNode` (lemmaNum p1 ?? lemmaNum p2 ?? ADD (opt f p1) (opt f p2))
opt f p@(SUB p1 p2) = f `atNode` (lemmaNum p1 ?? lemmaNum p2 ?? SUB (opt f p1) (opt f p2))
opt f p@(MUL p1 p2) = f `atNode` (lemmaNum p1 ?? lemmaNum p2 ?? MUL (opt f p1) (opt f p2))
opt f p@(DIV p1 p2) = f `atNode` (lemmaNum p1 ?? lemmaNum p2 ?? DIV (opt f p1) (opt f p2))

opt f p@(LINCOMB k1 p1 k2 p2) =
  f `atNode` (lemmaNum p1 ?? lemmaNum p2 ?? LINCOMB k1 (opt f p1) k2 (opt f p2))

opt f p@(NOT p1   ) = f `atNode` (lemmaLogic p1 ?? NOT (opt f p1))
opt f p@(AND p1 p2) = f `atNode` (lemmaLogic p1 ?? lemmaLogic p2 ?? AND (opt f p1) (opt f p2))
opt f p@(OR  p1 p2) = f `atNode` (lemmaLogic p1 ?? lemmaLogic p2 ?? OR  (opt f p1) (opt f p2))
opt f p@(XOR p1 p2) = f `atNode` (lemmaLogic p1 ?? lemmaLogic p2 ?? XOR (opt f p1) (opt f p2))

opt f p@(UnsafeNOT p1   ) = f `atNode` (lemmaLogic p1 ?? UnsafeNOT (opt f p1))
opt f p@(UnsafeAND p1 p2) = f `atNode` (lemmaLogic p1 ?? lemmaLogic p2 ?? UnsafeAND (opt f p1) (opt f p2))
opt f p@(UnsafeOR  p1 p2) = f `atNode` (lemmaLogic p1 ?? lemmaLogic p2 ?? UnsafeOR  (opt f p1) (opt f p2))
opt f p@(UnsafeXOR p1 p2) = f `atNode` (lemmaLogic p1 ?? lemmaLogic p2 ?? UnsafeXOR (opt f p1) (opt f p2))

opt f p@(ISZERO p1) = f `atNode` (lemmaNum p1 ?? ISZERO (opt f p1))
opt f p@(EQL p1 p2) = f `atNode` (lemmaNum p1 ?? lemmaNum p2 ?? EQL (opt f p1) (opt f p2))
opt f p@(EQLC p1 k) = f `atNode` (lemmaNum p1 ?? EQLC (opt f p1) k)

opt f p@(NIL _)     = f `atNode` p
opt f p@(CONS h ts) = f `atNode` (CONS (opt f h) (opt f ts))

-- How to apply a general optimization on an assertion
{-@ opt' :: Opt p -> Assertion p -> Assertion p @-}
opt' :: Opt p -> Assertion p -> Assertion p
opt' f (DEF s p τ) = DEF s (opt f p) τ
opt' f (NZERO p) = NZERO (opt f p)
opt' f (BOOL p) = BOOL (opt f p)
opt' f (EQA p1 p2) = EQA (opt f p1) (opt f p2)
