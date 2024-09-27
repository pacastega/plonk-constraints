{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# OPTIONS -Wno-unused-imports #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
module Main (main) where

import Data.FiniteField.PrimeField
import Vec

import Utils           -- needed to use reflected functions
import Circuits        -- needed to use reflected functions
import ArithmeticGates -- needed to use reflected functions
import LogicGates      -- needed to use reflected functions

import Constraints

import DSL
import WitnessGeneration

type F p = PrimeField p
type F17 = F 17
type FF  = F 2131


{-@ testProgram :: v:DSL _ (Btwn 0 7) @-}
testProgram :: DSL F17 Int
testProgram = ADD (ADD (WIRE 0) (WIRE 1)) (ADD (WIRE 2) (WIRE 3))

{-@ testProgram2 :: v:DSL _ (Btwn 0 7) @-}
testProgram2 :: DSL F17 Int
testProgram2 = MUL (ADD (WIRE 0) (CONST 15)) (ADD (WIRE 1) (CONST 3))

{-@ testProgram3 :: DSL _ (Btwn 0 6) @-}
testProgram3 :: DSL F17 Int
testProgram3 = DIV (WIRE 5) (WIRE 1)

{-@ testProgram4 :: DSL _ (Btwn 0 20) @-}
testProgram4 :: DSL F17 Int
testProgram4 = ISZERO (WIRE 0) `OR` (NOT (ISZERO (WIRE 0)) `AND` (ISZERO (WIRE 1)))

{-@ testProgram5 :: DSL _ (Btwn 0 20) @-}
testProgram5 :: DSL F17 Int
testProgram5 = (CONST 7 `MUL` WIRE 0) `EQL` CONST 1

{-@ testProgram6 :: DSL _ (Btwn 0 20) @-}
testProgram6 :: DSL F17 Int
testProgram6 = (WIRE 0 `ADD` CONST 2) `EQL` CONST 5

{-@ testProgram7 :: DSL _ (Btwn 0 20) @-}
testProgram7 :: DSL FF Int
testProgram7 = ITER (B 1 5) body (WIRE 1) where
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) | unpacked v} ->
              {v:DSL _ (Btwn 0 20) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int
  body = (\i p -> MUL p (WIRE 0))

{-@ testProgram8 :: DSL _ (Btwn 0 20) @-}
testProgram8 :: DSL FF Int
testProgram8 = ITER (B 2 5) body (CONST 1) where
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) | unpacked v} ->
              {v:DSL _ (Btwn 0 20) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int
  body = \i p -> MUL p (CONST $ fromIntegral i)

{-@ testProgram9 :: DSL _ (Btwn 0 20) @-}
testProgram9 :: DSL FF Int
testProgram9 = ITER (B 1 6) body (CONST 0) where
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) | unpacked v} ->
              {v:DSL _ (Btwn 0 20) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int
  body = \i p -> ADD p (CONST $ fromIntegral i)

{-@ testProgram10 :: Btwn 1 39 -> DSL _ (Btwn 0 40) @-}
testProgram10 :: Int -> DSL FF Int
testProgram10 nIters = ITER (B 1 nIters) body (CONST 0) where
  body = \i p -> WIRE i `ADD` (p `MUL` WIRE 0)
  {-@ body :: Btwn 1 40 ->
              {v:DSL _ (Btwn 0 40) | unpacked v} ->
              {v:DSL _ (Btwn 0 40) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int


{-@ testProgram11 :: DSL _ (Btwn 0 20) @-}
testProgram11 :: DSL FF Int
testProgram11 = (ITER (B 2 4) body (WIRE 0)) `EQL` (CONST 42) where
  body = \i p -> MUL p (WIRE 0)
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) | unpacked v} ->
              {v:DSL _ (Btwn 0 20) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int


{-@ testProgram12 :: {v:DSL _ (Btwn 0 20) | vlength v = 3} @-}
testProgram12 :: DSL FF Int
testProgram12 = (CONST 42)             `CONS`
                (CONST 4 `SUB` WIRE 0) `CONS`
                (WIRE 1 `ADD` CONST 5) `CONS` NIL


{-@ range :: lo:Int -> hi:{Int | hi >= lo} ->
             {res:DSL _ (Btwn 0 20) | isVector res && vlength res = hi-lo}
          / [hi-lo] @-}
range :: Int -> Int -> DSL FF Int
range a b = if a == b then NIL else CONST (fromIntegral a) `CONS` (range (a+1) b)

{-@ testProgram13 :: DSL _ (Btwn 0 20) @-}
testProgram13 :: DSL FF Int
testProgram13 = set (range 1 5) 2 (CONST 42) where

{-@ testProgram14 :: DSL _ (Btwn 0 20) @-}
testProgram14 :: DSL FF Int
testProgram14 = get (range 1 5) 3 where

{-@ vecMul :: {a:DSL _ (Btwn 0 20) | isVector a} ->
              {b:DSL _ (Btwn 0 20) | isVector b && vlength b = vlength a} ->
              {c:DSL _ (Btwn 0 20) | isVector c && vlength c = vlength a} @-}
vecMul :: DSL FF Int -> DSL FF Int -> DSL FF Int
vecMul (NIL)       (NIL)       = NIL
vecMul (CONS a as) (CONS b bs) = CONS (MUL a b) (vecMul as bs)

{-@ testProgram15 :: DSL _ (Btwn 0 20) @-}
testProgram15 :: DSL FF Int
testProgram15 = vecMul (range 1 4) (range 5 8)


cyan :: String -> String
cyan s = "\ESC[36m" ++ s ++ "\ESC[0m"


{-@ test :: m:Nat1 -> DSL _ (Btwn 0 m) -> (Btwn 0 m -> p) -> IO () @-}
test :: (Eq p, Fractional p, Show p) =>
        Int -> DSL p Int -> (Int -> p) -> IO ()
test m program valuation = do
  let labeledPrograms = label m (unpack $ desugar program)
  let circuit = concatMap (compile m) labeledPrograms
  let input = witnessGen m labeledPrograms valuation
  let output = map (\p -> input ! outputWire p) labeledPrograms

  putStrLn $ "Preprocessed program: " ++ show labeledPrograms
  putStrLn $ "Compiled circuit:     " ++ show circuit
  putStrLn $ "Input:                " ++ show input
  putStrLn $ "Final result: " ++ cyan (show output)

  putStrLn $ replicate 80 '='


main :: IO ()
main = do
  test 7 testProgram (const 1)
  test 7 testProgram2 (\case 0 -> 7; 1 -> 3; _ -> 0)
  test 6 testProgram3 (\case 5 -> 3; 1 -> 9; _ -> 0)

  test 20 testProgram4 (\case 0 -> 0; 1 -> 3; _ -> 7)
  test 20 testProgram4 (\case 0 -> 1; 1 -> 0; _ -> 7)
  test 20 testProgram4 (\case 0 -> 1; 1 -> 8; _ -> 7)

  test 20 testProgram5 (\case 0 -> 5; _ -> 8)
  test 20 testProgram5 (\case 0 -> 7; _ -> 8)

  test 20 testProgram6 (\case 0 -> 2; _ -> 0)
  test 20 testProgram6 (\case 0 -> 3; _ -> 0)

  test 20 testProgram7 (\case 0 -> 2; 1 -> 1; _ -> 0)
  test 20 testProgram7 (\case 0 -> 4; 1 -> 2; _ -> 0)

  test 20 testProgram8 (const 0)
  test 20 testProgram9 (const 0)

  test 40 (testProgram10 8) (\i -> if i == 0 then 2
                                   else if i > 8 then 0
                                   else [1,1,1,1,1,0,0,0] !! (i-1))
  test 40 (testProgram10 2) (\i -> if i == 0 then 16
                                   else if i > 2 then 0
                                   else [15, 8] !! (i-1))

  test 20 testProgram11 (const 627)

  test 20 testProgram12 (\i -> if i < 2 then [1,2] !! i else 0)

  test 20 testProgram13 (const 0)
  test 20 testProgram14 (const 0)
  test 20 testProgram15 (const 0)
