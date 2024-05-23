{-@ embed GHC.Num.Natural.Natural as int @-}
{-@ LIQUID "--reflection" @-}
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
type V17 = Vec F17


{-@ testProgram :: v:DSL _ (Btwn 0 7) _ @-}
testProgram :: DSL F17 Int F17
testProgram = ADD (ADD (WIRE 0) (WIRE 1)) (ADD (WIRE 2) (WIRE 3))

{-@ testInput :: VecN _ 7 @-}
testInput :: V17
testInput = fromList [1,1,1,1, -- input wires
                      4,       -- output wire
                      5,8]     -- incorrect intermediate wires

-- correct intermediate wires (automatically generated)
{-@ testInput' :: VecN _ 7 @-}
testInput' :: V17
testInput' = witnessGen 7 (label 7 testProgram) valuation where
  valuation = const 1


{-@ testProgram2 :: v:DSL _ (Btwn 0 7) _ @-}
testProgram2 :: DSL F17 Int F17
testProgram2 = MUL (ADD (WIRE 0) (CONST 15)) (ADD (WIRE 1) (CONST 3))

{-@ testInput2 :: VecN _ 7 @-}
testInput2 :: V17
testInput2 = fromList [7,3,        -- input wires
                       11,         -- output wire
                       5,15,6,3]   -- icorrect intermediate wires

-- correct intermediate wires (automatically generated)
{-@ testInput2' :: VecN _ 7 @-}
testInput2' :: V17
testInput2' = witnessGen 7 (label 7 testProgram2) valuation where
  valuation = \case 0 -> 7; 1 -> 3; _ -> 0


{-@ testProgram3 :: DSL _ (Btwn 0 6) _ @-}
testProgram3 :: DSL F17 Int F17
testProgram3 = DIV (WIRE 5) (WIRE 1)

{-@ testInput3 :: VecN _ 6 @-}
testInput3 :: V17
testInput3 = witnessGen 6 (label 6 testProgram3) valuation where
  valuation = \case 5 -> 3; 1 -> 9; _ -> 0


{-@ testProgram4 :: DSL _ (Btwn 0 20) _ @-}
testProgram4 :: DSL F17 Int Bool
testProgram4 = ISZERO (WIRE 0) `OR` (NOT (ISZERO (WIRE 0)) `AND` (ISZERO (WIRE 1)))

{-@ testInput4 :: VecN _ 20 @-}
testInput4 :: V17
testInput4 = witnessGen 20 (label 20 testProgram4) valuation where
  valuation = \case 0 -> 0; 1 -> 3; _ -> 7

{-@ testInput4' :: VecN _ 20 @-}
testInput4' :: V17
testInput4' = witnessGen 20 (label 20 testProgram4) valuation where
  valuation = \case 0 -> 1; 1 -> 0; _ -> 7

{-@ testInput4'' :: VecN _ 20 @-}
testInput4'' :: V17
testInput4'' = witnessGen 20 (label 20 testProgram4) valuation where
  valuation = \case 0 -> 1; 1 -> 8; _ -> 7


{-@ testProgram5 :: DSL _ (Btwn 0 20) _ @-}
testProgram5 :: DSL F17 Int Bool
testProgram5 = ISZERO ((CONST 7 `MUL` WIRE 0) `ADD` CONST (-1))

{-@ testInput5 :: VecN _ 20 @-}
testInput5 :: V17
testInput5 = witnessGen 20 (label 20 testProgram5) valuation where
  valuation = \case 0 -> 5; _ -> 8

{-@ testInput5' :: VecN _ 20 @-}
testInput5' :: V17
testInput5' = witnessGen 20 (label 20 testProgram5) valuation where
  valuation = \case 0 -> 7; _ -> 8


green :: String -> String
green s = "\ESC[32m" ++ s ++ "\ESC[0m"

red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"


{-@ test :: m:{v:Int | v >= 3} -> DSL _ (Btwn 0 m) t -> VecN _ m -> IO () @-}
test :: Int -> DSL F17 Int t -> V17 -> IO ()
test m program input = do
  let labeledProgram = label m program
  let circuit = compile m labeledProgram

  print labeledProgram
  print circuit

  let semantics_ = semanticsAreCorrect m labeledProgram input
  let satisfies_ = satisfies (nGates labeledProgram) m input circuit

  putStrLn $ "The given input is " ++ show input

  putStrLn $ "The high-level semantics of the program are " ++
    if semantics_ then green "correct" else red "incorrect"
  putStrLn $ "The given input " ++
    (if satisfies_ then green "satisfies" else red "doesn't satisfy") ++
    " the compiled circuit"
  putStrLn $ if semantics_ == satisfies_
    then green "SUCCESS!" else red "FAILURE"

  putStrLn $ "The final result is " ++ show (input ! outputWire labeledProgram)

  putStrLn $ replicate 80 '='


main :: IO ()
main = do
  test 7 testProgram testInput
  test 7 testProgram testInput'
  test 7 testProgram2 testInput2
  test 7 testProgram2 testInput2'
  test 6 testProgram3 testInput3

  test 20 testProgram4 testInput4
  test 20 testProgram4 testInput4'
  test 20 testProgram4 testInput4''

  test 20 testProgram5 testInput5
  test 20 testProgram5 testInput5'
