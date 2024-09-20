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

type F17 = PrimeField 17
type F p = PrimeField p


{-@ testProgram :: v:DSL _ (Btwn 0 7) _ @-}
testProgram :: DSL F17 Int F17
testProgram = ADD (ADD (WIRE 0) (WIRE 1)) (ADD (WIRE 2) (WIRE 3))

{-@ testProgram2 :: v:DSL _ (Btwn 0 7) _ @-}
testProgram2 :: DSL F17 Int F17
testProgram2 = MUL (ADD (WIRE 0) (CONST 15)) (ADD (WIRE 1) (CONST 3))

{-@ testProgram3 :: DSL _ (Btwn 0 6) _ @-}
testProgram3 :: DSL F17 Int F17
testProgram3 = DIV (WIRE 5) (WIRE 1)

{-@ testProgram4 :: DSL _ (Btwn 0 20) _ @-}
testProgram4 :: DSL F17 Int Bool
testProgram4 = ISZERO (WIRE 0) `OR` (NOT (ISZERO (WIRE 0)) `AND` (ISZERO (WIRE 1)))

{-@ testProgram5 :: DSL _ (Btwn 0 20) _ @-}
testProgram5 :: DSL F17 Int Bool
testProgram5 = (CONST 7 `MUL` WIRE 0) `EQL` CONST 1

{-@ testProgram6 :: DSL _ (Btwn 0 20) _ @-}
testProgram6 :: DSL F17 Int Bool
testProgram6 = (WIRE 0 `ADD` CONST 2) `EQL` CONST 5

{-@ testProgram7 :: DSL _ (Btwn 0 20) _ @-}
testProgram7 :: DSL (F 2131) Int (F 2131)
testProgram7 = ITER (B 1 5) body (WIRE 1) where
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) _ | unpacked v} ->
              {v:DSL _ (Btwn 0 20) _ | unpacked v} @-}
  body :: Int -> DSL (F 2131) Int (F 2131) -> DSL (F 2131) Int (F 2131)
  body = (\i p -> MUL p (WIRE 0))

{-@ testProgram8 :: DSL _ (Btwn 0 20) _ @-}
testProgram8 :: DSL (F 2131) Int (F 2131)
testProgram8 = ITER (B 2 5) body (CONST 1) where
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) _ | unpacked v} ->
              {v:DSL _ (Btwn 0 20) _ | unpacked v} @-}
  body :: Int -> DSL (F 2131) Int (F 2131) -> DSL (F 2131) Int (F 2131)
  body = \i p -> MUL p (CONST $ fromIntegral i)

{-@ testProgram9 :: DSL _ (Btwn 0 20) _ @-}
testProgram9 :: DSL (F 2131) Int (F 2131)
testProgram9 = ITER (B 1 6) body (CONST 0) where
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) _ | unpacked v} ->
              {v:DSL _ (Btwn 0 20) _ | unpacked v} @-}
  body :: Int -> DSL (F 2131) Int (F 2131) -> DSL (F 2131) Int (F 2131)
  body = \i p -> ADD p (CONST $ fromIntegral i)

{-@ testProgram10 :: Btwn 1 39 -> DSL _ (Btwn 0 40) _ @-}
testProgram10 :: Int -> DSL (F 2131) Int (F 2131)
testProgram10 nIters = ITER (B 1 nIters) body (CONST 0) where
  body = \i p -> WIRE i `ADD` (p `MUL` WIRE 0)
  {-@ body :: Btwn 1 40 ->
              {v:DSL _ (Btwn 0 40) _ | unpacked v} ->
              {v:DSL _ (Btwn 0 40) _ | unpacked v} @-}
  body :: Int -> DSL (F 2131) Int (F 2131) -> DSL (F 2131) Int (F 2131)


{-@ testProgram11 :: DSL _ (Btwn 0 20) _ @-}
testProgram11 :: DSL (F 2131) Int Bool
testProgram11 = (ITER (B 2 4) body (WIRE 0)) `EQL` (CONST 42) where
  body = \i p -> MUL p (WIRE 0)
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) _ | unpacked v} ->
              {v:DSL _ (Btwn 0 20) _ | unpacked v} @-}
  body :: Int -> DSL (F 2131) Int (F 2131) -> DSL (F 2131) Int (F 2131)


cyan :: String -> String
cyan s = "\ESC[36m" ++ s ++ "\ESC[0m"


{-@ test :: m:Nat1 -> DSL _ (Btwn 0 m) t -> (Btwn 0 m -> p) -> IO () @-}
test :: (Eq p, Fractional p, Show p) =>
        Int -> DSL p Int t -> (Int -> p) -> IO ()
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
