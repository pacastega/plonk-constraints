{-@ embed GHC.Num.Natural.Natural as int @-}
{-@ LIQUID "--reflection" @-}
{-# OPTIONS -Wno-unused-imports #-}
{-# LANGUAGE DataKinds #-}
module Main (main) where

import Data.FiniteField.PrimeField
import Vec

import Utils           -- needed to use reflected functions
import Circuits        -- needed to use reflected functions
import ArithmeticGates -- needed to use reflected functions

import Constraints

import DSL

type F17 = PrimeField 17
type V17 = Vec F17


{-@ testProgram :: v:DSL _ (Btwn 0 7) @-}
testProgram :: DSL F17 Int
testProgram = ADD (ADD (WIRE 0) (WIRE 1)) (ADD (WIRE 2) (WIRE 3))

{-@ testInput :: VecN _ 7 @-}
testInput :: V17
testInput = fromList [1,1,1,1, -- input wires
                      4,       -- output wire
                      5,8]     -- incorrect intermediate wires

{-@ testInput' :: VecN _ 7 @-}
testInput' :: V17
testInput' = fromList [1,1,1,1, -- input wires
                       4,       -- output wire
                       2,2]     -- correct intermediate wires


{-@ testProgram2 :: v:DSL _ (Btwn 0 7) @-}
testProgram2 :: DSL F17 Int
testProgram2 = MUL (ADD (WIRE 0) (CONST 15)) (ADD (WIRE 1) (CONST 3))

{-@ testInput2 :: VecN _ 7 @-}
testInput2 :: V17
testInput2 = fromList [7,3,        -- input wires
                       11,         -- output wire
                       5,15,6,3]   -- icorrect intermediate wires

{-@ testInput2' :: VecN _ 7 @-}
testInput2' :: V17
testInput2' = fromList [7,3,      -- input wires
                        13,       -- output wire
                        5,15,6,3] -- correct intermediate wires


green :: String -> String
green s = "\ESC[32m" ++ s ++ "\ESC[0m"

red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"


{-@ test :: m:{v:Int | v >= 3} -> DSL _ (Btwn 0 m) -> VecN _ m -> IO () @-}
test :: Int -> DSL F17 Int -> V17 -> IO ()
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

  putStrLn $ replicate 80 '='


main :: IO ()
main = do
  test 7 testProgram testInput
  test 7 testProgram testInput'
  test 7 testProgram2 testInput2
  test 7 testProgram2 testInput2'
