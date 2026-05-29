{-# LANGUAGE ScopedTypeVariables, CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Semantics2 where

import TypeAliases
import DSL
import Utils
import Vec
import Semantics

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S


--TODO: move this to Semantics
{-@ reflect holds @-}
{-@ holds :: a:Assertion p -> NameValuation p -> Bool @-}
holds :: (Fractional p, Eq p) => Assertion p -> NameValuation p -> Bool
holds a ρ = case a of
  NZERO e1 | Just _ <- inferType e1
           , Just (VF v1) <- eval e1 ρ
          -> v1 /= 0
  BOOLEAN e1 | Just _ <- inferType e1
             , Just (VF v1) <- eval e1 ρ
            -> boolean v1
  EQA e1 e2 | Just _ <- inferType e1 , Just _ <- inferType e2
            , Just (VF v1) <- eval e1 ρ
            , Just (VF v2) <- eval e2 ρ
           -> v1 == v2
  _ -> False


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
