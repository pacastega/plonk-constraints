{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Optimizations (optimize) where

import Data.Maybe (fromMaybe)
import Control.Applicative ((<|>))
import Control.Monad ((>=>))

import DSL
import GlobalStore
import Utils (boolean, any', (??), foldr')

import Optimizations.ConstantFolding (constantFolding)
import Optimizations.RemoveConstants (removeConstants)
import Optimizations.Base

import Language.Haskell.Liquid.ProofCombinators

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

{-@ compatibleRefl :: d:TypedDSL p -> { compatible d d } @-}
compatibleRefl :: DSL p -> Proof
compatibleRefl program = case inferType program of
  Nothing -> trivial
  Just τ -> subtype τ τ *** QED

-- Try to apply optimization `f` at node `p`; if it fails, leave `p` unchanged
{-@ atNode :: Opt p -> d:TypedDSL p -> {v:TypedDSL p | compatible v d} @-}
atNode :: Opt p -> DSL p -> DSL p
atNode f p = case f p of
  Nothing -> p ? compatibleRefl p
  Just p' -> p'

-- Combine two optimizations to apply them 'in parallel': if the first fails,
-- try the second one
{-@ (|||) :: Opt p -> Opt p -> Opt p @-}
(|||) :: Opt p -> Opt p -> Opt p
(|||) f1 f2 p = f1 p <|> f2 p

-- compatible with something numeric is also numeric
{-@ compNum :: d1:{DSL p | numeric d1} -> d2:{DSL p | compatible d2 d1}
             -> { numeric d2 } @-}
compNum :: DSL p -> DSL p -> Proof
compNum d1 d2 = case (inferType d1, inferType d2) of
  -- the proof is trivial by case analysis
  (Just TF,   Just TF)   -> trivial
  (Just TF,   Just TBit) -> trivial
  (Just TBit, Just TBit) -> trivial
  (_,         _)         -> error "unreachable"

-- compatible with something logic has the same type
{-@ compLogic :: d1:{DSL p | logic d1} -> d2:{DSL p | compatible d2 d1}
               -> { inferType d2 == inferType d1 } @-}
compLogic :: DSL p -> DSL p -> Proof
compLogic d1 d2 = case (inferType d1, inferType d2) of
  -- the proof is trivial by case analysis
  (Just TBool, Just TBool) -> trivial
  -- (Just TBool, Just TBit)  -> trivial
  (Just TBit,  Just TBit)  -> trivial
  (_,          _)          -> error "unreachable"

-- compatible with a scalar is also scalar
{-@ compScalar :: d1:{DSL p | scalar d1} -> d2:{DSL p | compatible d2 d1}
                -> { scalar d2 } @-}
compScalar :: DSL p -> DSL p -> Proof
compScalar d1 d2 = case (inferType d1, inferType d2) of
  (Just (TVec _), Just (TVec _)) -> error "unreachable"
  (Just _,        Just _)        -> trivial
  (_,             _)             -> error "unreachable"

-- How to apply a general optimization on a program
{-@ opt :: Opt p -> d:TypedDSL p -> {v:TypedDSL p | compatible v d} @-}
opt :: Opt p -> DSL p -> DSL p
opt f p@VAR {}       = f `atNode` p
opt f p@(CONST {})   = f `atNode` p
opt f p@(BOOLEAN {}) = f `atNode` p
opt f p@(BIT {})     = f `atNode` p

opt f p@(ADD p1 p2) = f `atNode` (let p1' = numeric p1 ?? opt f p1
                                      p2' = numeric p2 ?? opt f p2
                                  in ADD p1' p2' ? compNum p1 p1'
                                                 ? compNum p2 p2')
opt f p@(SUB p1 p2) = f `atNode` (let p1' = numeric p1 ?? opt f p1
                                      p2' = numeric p2 ?? opt f p2
                                  in SUB p1' p2' ? compNum p1 p1'
                                                 ? compNum p2 p2')
opt f p@(MUL p1 p2) = f `atNode` (let p1' = numeric p1 ?? opt f p1
                                      p2' = numeric p2 ?? opt f p2
                                  in MUL p1' p2' ? compNum p1 p1'
                                                 ? compNum p2 p2')
opt f p@(DIV p1 p2) = f `atNode` (let p1' = numeric p1 ?? opt f p1
                                      p2' = numeric p2 ?? opt f p2
                                  in DIV p1' p2' ? compNum p1 p1'
                                                 ? compNum p2 p2')

opt f p@(ADDC p1 k) = f `atNode` (let p1' = opt f p1
                                  in ADDC p1' k ? compNum p1 p1')
opt f p@(MULC p1 k) = f `atNode` (let p1' = opt f p1
                                  in MULC p1' k ? compNum p1 p1')
opt f p@(LINCOMB k1 p1 k2 p2) =
  f `atNode` (let p1' = opt f p1
                  p2' = numeric p2 ?? opt f p2
              in LINCOMB k1 p1' k2 p2' ? compNum p1 p1' ? compNum p2 p2')

opt f p@(NOT p1)    = f `atNode` (let p1' = opt f p1
                                  in NOT p1' ? compLogic p1 p1')
opt f p@(AND p1 p2) = f `atNode` (let p1' = opt f p1; p2' = opt f p2
                                  in AND p1' p2' ? compLogic p1 p1'
                                                 ? compLogic p2 p2')
opt f p@(OR  p1 p2) = f `atNode` (let p1' = opt f p1; p2' = opt f p2
                                  in OR  p1' p2' ? compLogic p1 p1'
                                                 ? compLogic p2 p2')
opt f p@(XOR p1 p2) = f `atNode` (let p1' = opt f p1; p2' = opt f p2
                                  in XOR p1' p2' ? compLogic p1 p1'
                                                 ? compLogic p2 p2')

opt f p@(UnsafeNOT p1   ) = f `atNode` (let p1' = opt f p1
                                        in UnsafeNOT p1' ? compLogic p1 p1')
opt f p@(UnsafeAND p1 p2) = f `atNode` (let p1' = opt f p1; p2' = opt f p2
                                  in UnsafeAND p1' p2' ? compLogic p1 p1'
                                                       ? compLogic p2 p2')
opt f p@(UnsafeOR  p1 p2) = f `atNode` (let p1' = opt f p1; p2' = opt f p2
                                  in UnsafeOR p1' p2' ? compLogic p1 p1'
                                                      ? compLogic p2 p2')
opt f p@(UnsafeXOR p1 p2) = f `atNode` (let p1' = opt f p1; p2' = opt f p2
                                  in UnsafeXOR p1' p2' ? compLogic p1 p1'
                                                       ? compLogic p2 p2')

opt f p@(ISZERO p1) = f `atNode` (let p1' = opt f p1
                                  in ISZERO p1' ? compNum p1 p1')
opt f p@(EQL p1 p2) = f `atNode` (let p1' = opt f p1
                                      p2' = numeric p2 ?? opt f p2
                                  in EQL p1' p2' ? compNum p1 p1'
                                                 ? compNum p2 p2')
opt f p@(EQLC p1 k) = f `atNode` (let p1' = opt f p1
                                  in EQLC p1' k ? compNum p1 p1')

opt f p@(NIL _)     = f `atNode` p
opt f p@(CONS h ts) = f `atNode` (CONS (opt f h) (opt f ts))

-- How to apply a general optimization on an assertion
{-@ opt' :: Opt p -> Assertion p -> Assertion p @-}
opt' :: Opt p -> Assertion p -> Assertion p
opt' f (DEF s p τ) = let p' = opt f p in compScalar p p' ?? DEF s p' τ
opt' f (NZERO p) = let p' = opt f p in compScalar p p' ?? NZERO p'
opt' f (BOOL p) = let p' = opt f p in compScalar p p' ?? BOOL p'
opt' f (EQA p1 p2) = let p1' = opt f p1
                         p2' = opt f p2
                     in compScalar p1 p1' ?? compScalar p2 p2' ?? EQA p1' p2'
