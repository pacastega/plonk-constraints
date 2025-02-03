{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ LIQUID "--max-case-expand=0" @-}
module Optimizations (optimize) where

import Data.Maybe (fromMaybe)
import Control.Applicative ((<|>))

import DSL
import GlobalStore
import Utils (boolean, any', (??))

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
optimize program = optimize' (foldr' compose Just optimizations) program where
  {-@ optimize' :: Opt p -> GlobalStore p ({d:DSL p | wellTyped d})
                -> GlobalStore p ({d:DSL p | wellTyped d}) @-}
  optimize' :: Opt p -> GlobalStore p (DSL p) -> GlobalStore p (DSL p)
  optimize' f (GStore body store hints) =
    GStore (opt f body) (map (opt' f) store) hints

  {-@ foldr' :: (Opt p -> Opt p -> Opt p) -> Opt p -> [Opt p] -> Opt p @-}
  foldr' :: (Opt p -> Opt p -> Opt p) -> Opt p -> [Opt p] -> Opt p
  foldr' = foldr

{-@ compose :: Opt p -> Opt p -> Opt p @-}
compose :: Opt p -> Opt p -> Opt p
compose f g x = case f x of
  Nothing -> Nothing
  Just y  -> g y

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
opt f p@VAR {}     = f `atNode` p
opt f p@CONST {}   = f `atNode` p
opt f p@BOOLEAN {} = f `atNode` p

opt f (ADD p1 p2) = f `atNode` (ADD (opt f p1) (opt f p2))
opt f (SUB p1 p2) = f `atNode` (SUB (opt f p1) (opt f p2))
opt f (MUL p1 p2) = f `atNode` (MUL (opt f p1) (opt f p2))
opt f (DIV p1 p2) = f `atNode` (DIV (opt f p1) (opt f p2))

opt f (ADDC p k) = f `atNode` (ADDC (opt f p) k)
opt f (MULC p k) = f `atNode` (MULC (opt f p) k)
opt f (LINCOMB k1 p1 k2 p2) =
  f `atNode` (LINCOMB k1 (opt f p1) k2 (opt f p2))

opt f (NOT p1   ) = f `atNode` (NOT (opt f p1))
opt f (AND p1 p2) = f `atNode` (AND (opt f p1) (opt f p2))
opt f (OR  p1 p2) = f `atNode` (OR  (opt f p1) (opt f p2))
opt f (XOR p1 p2) = f `atNode` (XOR (opt f p1) (opt f p2))

opt f (UnsafeNOT p1   ) = f `atNode` (UnsafeNOT (opt f p1))
opt f (UnsafeAND p1 p2) = f `atNode` (UnsafeAND (opt f p1) (opt f p2))
opt f (UnsafeOR  p1 p2) = f `atNode` (UnsafeOR  (opt f p1) (opt f p2))
opt f (UnsafeXOR p1 p2) = f `atNode` (UnsafeXOR (opt f p1) (opt f p2))

opt f (ISZERO p1) = f `atNode` (ISZERO (opt f p1))
opt f (EQL p1 p2) = f `atNode` (EQL (opt f p1) (opt f p2))
opt f (EQLC p1 k) = f `atNode` (EQLC (opt f p1) k)

opt f p@NIL {}    = f `atNode` p
opt f (CONS h ts) = f `atNode` (CONS (opt f h) (opt f ts))

opt f (BoolToF p) = f `atNode` (BoolToF (opt f p))

-- How to apply a general optimization on an assertion
{-@ opt' :: Opt p -> Assertion p -> Assertion p @-}
opt' :: Opt p -> Assertion p -> Assertion p
opt' f (DEF s p τ) = DEF s (opt f p) τ
opt' f (NZERO p) = NZERO (opt f p)
opt' f (BOOL p) = BOOL (opt f p)
opt' f (EQA p1 p2) = EQA (opt f p1) (opt f p2)
