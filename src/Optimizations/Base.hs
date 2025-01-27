{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Optimizations.Base where

import DSL
import Utils (any')

import Language.Haskell.Liquid.ProofCombinators

type Opt p = DSL p -> Maybe (DSL p)
{-@ type Opt p = d:TypedDSL p -> Maybe ({v:TypedDSL p | sameType v d}) @-}
