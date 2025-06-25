{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Optimizations.RemoveConstants (removeConstants) where

import Optimizations.Base (Opt)
import DSL
import Semantics
import Utils (any', liftA2', fmap')

import Data.Maybe (isJust)

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect removeConstants @-}
{-@ removeConstants :: Opt p @-}
removeConstants :: (Fractional p, Eq p) => DSL p -> Maybe (DSL p)
removeConstants (ADD arg1 arg2) = case arg1 of
  -- linear combinations
  MULC p1 k1 -> case arg2 of
    MULC p2 k2 -> let p' = LINCOMB k1 p1 k2 p2 in Just p'
    p2         -> let p' = LINCOMB k1 p1 1  p2 in Just p'

  CONST 0 -> Just arg2
  CONST k -> let p' = ADDC arg2 k in Just p'

  p1 -> case arg2 of
    MULC p2 k2 -> let p' = LINCOMB 1  p1 k2 p2 in Just p'

    CONST 0 -> Just p1
    CONST k -> let p' = ADDC arg1 k in Just p'

    _ -> Nothing

removeConstants (ADDC p1 0) = Just p1

removeConstants (SUB arg1 arg2) = case (arg1,arg2) of
  -- subtracting 0 is a no-op
  (p1, CONST 0) -> let p' = p1 in Just p'
  -- subtracting a constant can be done more efficiently
  (p1, CONST k) -> let p' = (ADDC p1 (-k)) in Just p'

  _ -> Nothing

removeConstants (MUL arg1 arg2) = case arg1 of

  CONST 1 -> let p' = arg2 in Just p'
  CONST 0 -> let p' = CONST 0 in Just p'
  CONST k -> let p' = MULC arg2 k in Just p'

  _ -> case arg2 of
    CONST 1 -> let p' = arg1 in Just p'
    CONST 0 -> let p' = CONST 0 in Just p'
    CONST k -> let p' = MULC arg1 k in Just p'

    _ -> Nothing

removeConstants (MULC _  0) = Just (CONST 0)
removeConstants (MULC p1 1) = Just p1

removeConstants (DIV arg1 arg2) = case (arg1,arg2) of
  -- dividing by 1 is a no-op
  (p1, CONST 1) -> let p' = p1 in Just p'
  -- TODO: dividing by a constant can be done more efficiently
  -- (p1, CONST k) | k /= 0 -> let p' = MULC p1 (1/k) in Just p'

  _ -> Nothing

removeConstants (EQL arg1 arg2) = case (arg1,arg2) of
  -- checking equality against a constant can be done more efficiently
  (p, CONST k) -> Just (EQLC p k)
  (CONST k, p) -> Just (EQLC p k)

  _ -> Nothing

removeConstants _ = Nothing -- any other pattern is not a redex

{-@ reflect isJust @-}

{-@ removeConstantsProof :: ρ:NameValuation p
         -> d1:TypedDSL p
         -> d2:{TypedDSL p | removeConstants d1 = Just d2}
         -> { isJust (eval d1 ρ) =>
              eval d1 ρ = eval d2 ρ } @-}
removeConstantsProof :: (Fractional p, Eq p)
                     => NameValuation p -> DSL p -> DSL p -> Proof
removeConstantsProof ρ (ADD arg1 arg2) _ = case arg1 of
  -- linear combinations
  MULC p1 _ -> case arg2 of
    MULC p2 _ -> case (eval p1 ρ, eval p2 ρ) of (Just _, Just _) -> (); _ -> ()
    p2         -> case (eval p1 ρ, eval p2 ρ) of (Just _, Just _) -> (); _ -> ()

  CONST 0 -> case (eval arg2 ρ) of (Just _) -> (); _ -> ()
  CONST _ -> trivial

  p1 -> case arg2 of
    MULC p2 _ -> case (eval p1 ρ, eval p2 ρ) of (Just _, Just _) -> (); _ -> ()

    CONST 0 -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
    CONST _ -> case (eval p1 ρ) of (Just _) -> (); _ -> ()

removeConstantsProof ρ (ADDC p1 _) _ =
  case (eval p1 ρ) of (Just _) -> (); _ -> ()

removeConstantsProof ρ (SUB arg1 arg2) _ = case (arg1,arg2) of
  -- subtracting 0 is a no-op
  (p1, CONST 0) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
  -- subtracting a constant can be done more efficiently
  (p1, CONST _) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()

removeConstantsProof ρ (MUL arg1 arg2) _ = case arg1 of

  CONST 1 -> case (eval arg2 ρ) of (Just _) -> (); _ -> ()
  CONST 0 -> case (eval arg2 ρ) of (Just _) -> (); _ -> ()
  CONST _ -> trivial

  p1 -> case arg2 of
    CONST 1 -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
    CONST 0 -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
    CONST _ -> case (eval p1 ρ) of (Just _) -> (); _ -> ()

removeConstantsProof ρ (MULC p1 _) _ =
  case (eval p1 ρ) of (Just _) -> (); _ -> ()

removeConstantsProof ρ (DIV arg1 arg2) _ = case (arg1,arg2) of
  -- dividing by 1 is a no-op
  (p1, CONST 1) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
  -- TODO: dividing by a constant can be done more efficiently
  -- (p1, CONST k) -> case (eval p1 ρ) of (Just x) -> (); _ -> ()

removeConstantsProof ρ (EQL arg1 arg2) _ = case (arg1,arg2) of
  -- checking equality against a constant can be done more efficiently
  (p1, CONST _) -> case (eval p1 ρ) of (Just _) -> (); _ -> ()
  (CONST _, _) -> trivial
