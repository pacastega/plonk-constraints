{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Optimizations.Base where

import DSL
import Language.Haskell.Liquid.ProofCombinators

-- an optimization always gives a more concrete type
type Opt p = DSL p -> Maybe (DSL p)
{-@ type Opt p = d:TypedDSL p -> Maybe ({v:TypedDSL p | compatible v d}) @-}

{-@ lemmaRefl :: { subtype TBit TBit
                && subtype TF TF
                && subtype TBool TBool
                 } @-}
lemmaRefl :: Proof
lemmaRefl = trivial
