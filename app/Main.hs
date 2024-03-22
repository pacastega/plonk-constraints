{-@ embed GHC.Num.Natural.Natural as int @-}
{-@ LIQUID "--reflection" @-}
{-# LANGUAGE DataKinds #-}
module Main (main) where

import Data.FiniteField.PrimeField
import Vec
import Utils (allRange) -- needed to use ‘satisfies’ in the reflection
import Constraints

import DSL

type V17 = Vec (PrimeField 17)


{-@ testProgram :: {v:DSL _ (Btwn Int 0 7) | nGates v == 3 } @-}
testProgram :: DSL 17 Int
testProgram = ADD (ADD (WIRE 0) (WIRE 1)) (ADD (WIRE 2) (WIRE 3))

{-@ testInput :: VecN _ 7 @-}
testInput :: V17
testInput = fromList [1,1,1,1, -- input wires
                      4,       -- output wire
                      5,8]     -- intermediate wires: any value at all satisfies
                               -- the ‘high-level’ specification, even though it
                               -- may not satisfy the circuit itself.

-- OPTION 2: hard-code the compiled circuit -----------------------------------
-- A workaround is to hard-code the output of the compile function and do the
-- type checking here (the type checking itself seems to work fine). The issue
-- now is that there is some problem with ‘circuit’: printing the circuit, or
-- trying to use it in the ‘satisfies’ function below (line 77) leads to this
-- compile-time error:

-- /home/pablo/programs/liquid-haskell/plonk-constraints/app/Main.hs:77:44: error:
--     • Uh oh.
--     (Another Broken Test!!!) splitc unexpected:
-- rHole
--   <:
-- (RApp Data.FiniteField.PrimeField.PrimeField<[]>(RApp GHC.Types.Int<[]>))
--     •
--    |
-- 77 |   let satisfies_ = satisfies 3 7 testInput circuit
--    |                                            ^^^^^^^


-- {-@ circuit :: Circuit _ 3 7 @-}
-- circuit :: Circuit (PrimeField 17)
-- circuit = let f = fromList in
--   ([f [5,0,2], f [6,1,3], f [4,5,6]],
--    [f [1,1,1], f [1,1,1], f [16,16,16], f [0,0,0], f [0,0,0]])

-- outputWire :: Int
-- outputWire = 4
-------------------------------------------------------------------------------

main :: IO ()
main = do

  -- OPTION 1: use the compile function ---------------------------------------
  -- This should be the preferred version. The issue is that LH doesn’t know
  -- that circuit has the correct dimensions:
  -- the inferred type {v:... | vvlen v >= 0}
  -- is not a subtype of the required type {v:... | vvlen == 3}.

  -- I think there must be some error somewhere because the refinement of
  -- compile does include information about the number of gates of the generated
  -- circuit: it is exactly ‘nGates c’, where ‘c’ is the input program, and line
  -- 79 below shows that nGates returns 3 on the test program (for this, lines
  -- 84 and 85 must be commented out, so the code compiles).


  let (circuit, outputWire) = compile 7 testProgram
  -----------------------------------------------------------------------------

  let semantics_ = semantics testProgram (testInput !) == testInput ! outputWire
  let satisfies_ = satisfies 3 7 testInput circuit

  putStrLn $ "The program needs " ++ show (nGates testProgram) ++ " gates"

  print (circuit, outputWire)
  putStrLn $ "The high-level semantics of the program are " ++ if semantics_
    then "correct" else "incorrect"
  putStrLn $ "The given input " ++ if satisfies_
    then "satisfies" else "doesn't satisfy" ++ " the compiled circuit"
