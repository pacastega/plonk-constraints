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
opt f p@BOOL  {}   = f `atNode` p

opt f (UN op p1) = f `atNode` (UN op (opt f p1))
opt f (BIN op p1 p2) = f `atNode` (BIN op (opt f p1) (opt f p2))

opt f p@NIL {}    = f `atNode` p
opt f (CONS h ts) = f `atNode` (CONS (opt f h) (opt f ts))


-- How to apply a general optimization on an assertion
{-@ opt' :: Opt p -> Assertion p -> Assertion p @-}
opt' :: Opt p -> Assertion p -> Assertion p
opt' f (NZERO p) = NZERO (opt f p)
opt' f (BOOLEAN p) = BOOLEAN (opt f p)
opt' f (EQA p1 p2) = EQA (opt f p1) (opt f p2)
