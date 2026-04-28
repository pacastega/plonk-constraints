{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}

module TypeAliases where
import GHC.Num.Integer (Integer (IS))

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

{-@ type Nat1 = {v:Int | v >= 1} @-}

{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type Btwn A B = {v:Int | A <= v && v < B} @-} -- [A..B)

{-@ type TRUE = {b:Bool | b} @-}

{-@ define fromInteger x = (x) @-}
{-@ define IS x = (x) @-}

-- Valuation & environment aliases ---------------------------------------------

-- σ ~~ valuation for wires (wire index ↦ value)
type WireValuation p = M.Map Int p
{-@ type WireValuation p M = M.Map (Btwn 0 M) p @-}

-- ρ ~~ valuation for variables (variable name ↦ value)
type NameValuation p = M.Map String p

-- Λ ~~ labeling environment (variable name ↦ wire index)
type LabelEnv p i = M.Map String i


-- "Agreement" relation between ρ and σ valuations ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- ∀x ∈ dom(Λ) . ρ(x) = σ(Λ(x))
{-@ type Agree Λ Ρ Σ = var:{String | M.member var Λ}
                    -> {(M.lookup var Ρ = M.lookup (M.lookup' var Λ) Σ)} @-}

-- "Greater than or equal" relation between maps ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

{-@ type MapGE M2 M1 = k:{Int | M.member k M1}
                    -> { M.member k M2 && M.lookup' k M1 = M.lookup' k M2 } @-}
