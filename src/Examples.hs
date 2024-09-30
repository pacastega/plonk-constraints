{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# OPTIONS -Wno-unused-imports #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module Examples (testArithmetic, testBoolean, testLoops, testVectors) where

import Data.FiniteField.PrimeField
import Vec
import PlinkLib

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

-- Generic test function -------------------------------------------------------
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

-- Arithmetic programs ---------------------------------------------------------
-- (x0 + x1) + (x2 + x3)
{-@ arith1 :: v:DSL _ (Btwn 0 7) @-}
arith1 :: DSL F17 Int
arith1 = ADD (ADD (WIRE 0) (WIRE 1)) (ADD (WIRE 2) (WIRE 3))

-- (x0 + 15) * (x1 + 3)
{-@ arith2 :: v:DSL _ (Btwn 0 7) @-}
arith2 :: DSL F17 Int
arith2 = MUL (ADD (WIRE 0) (CONST 15)) (ADD (WIRE 1) (CONST 3))

-- x5 / x1
{-@ arith3 :: DSL _ (Btwn 0 6) @-}
arith3 :: DSL F17 Int
arith3 = DIV (WIRE 5) (WIRE 1)

testArithmetic :: IO ()
testArithmetic = do
  test 7 arith1 (const 1)                      -- (1+1)  + (1+1) = 4
  test 7 arith2 (\case 0 -> 7; 1 -> 3; _ -> 0) -- (7+15) * (3+3) = 13
  test 6 arith3 (\case 5 -> 3; 1 -> 9; _ -> 0) -- 3 / 9          = 6

-- Boolean programs ------------------------------------------------------------
-- x0 == 0 || (x0 /= 0 && x1 == 1)
{-@ bool1 :: DSL _ (Btwn 0 20) @-}
bool1 :: DSL F17 Int
bool1 = ISZERO (WIRE 0) `OR` (NOT (ISZERO (WIRE 0)) `AND` (ISZERO (WIRE 1)))

-- 7 * x0 == 1
{-@ bool2 :: DSL _ (Btwn 0 20) @-}
bool2 :: DSL F17 Int
bool2 = (CONST 7 `MUL` WIRE 0) `EQL` CONST 1

-- x0 + 2 == 5
{-@ bool3 :: DSL _ (Btwn 0 20) @-}
bool3 :: DSL F17 Int
bool3 = (WIRE 0 `ADD` CONST 2) `EQL` CONST 5

testBoolean :: IO ()
testBoolean = do
  test 20 bool1 (\case 0 -> 0; 1 -> 3; _ -> 7) -- x0 == 0
  test 20 bool1 (\case 0 -> 1; 1 -> 0; _ -> 7) -- x0 /= 0 && x1 == 0
  test 20 bool1 (\case 0 -> 1; 1 -> 8; _ -> 7) -- x0 /= 0 && x1 /= 0

  test 20 bool2 (\case 0 -> 5; _ -> 8) -- 7 * 5 == 1 (== True)
  test 20 bool2 (\case 0 -> 7; _ -> 8) -- 7 * 7 == 1 (== False)

  test 20 bool3 (\case 0 -> 2; _ -> 0) -- 2 + 2 == 5 (== False)
  test 20 bool3 (\case 0 -> 3; _ -> 0) -- 3 + 2 == 5 (== True)

-- Loop programs ---------------------------------------------------------------
-- x1 * (x0)^5
{-@ loop1 :: DSL _ (Btwn 0 20) @-}
loop1 :: DSL FF Int
loop1 = ITER (B 1 5) body (WIRE 1) where
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) | unpacked v} ->
              {v:DSL _ (Btwn 0 20) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int
  body = (\_ p -> MUL p (WIRE 0))

-- 5! = 120
{-@ loop2 :: DSL _ (Btwn 0 20) @-}
loop2 :: DSL FF Int
loop2 = ITER (B 2 5) body (CONST 1) where
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) | unpacked v} ->
              {v:DSL _ (Btwn 0 20) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int
  body = \i p -> MUL p (CONST $ fromIntegral i)

-- 1 + 2 + 3 + 4 + 5 + 6 = 21
{-@ loop3 :: DSL _ (Btwn 0 20) @-}
loop3 :: DSL FF Int
loop3 = ITER (B 1 6) body (CONST 0) where
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) | unpacked v} ->
              {v:DSL _ (Btwn 0 20) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int
  body = \i p -> ADD p (CONST $ fromIntegral i)

-- Polynomial evaluation:
-- let x = x_0 in (x_1 * x^(n-1) + x_2 * x^(n-2) + ... + x_(n-1) * x + x_n)
{-@ loop4 :: Btwn 1 39 -> DSL _ (Btwn 0 40) @-}
loop4 :: Int -> DSL FF Int
loop4 n = ITER (B 1 n) body (CONST 0) where
  body = \i p -> WIRE i `ADD` (p `MUL` WIRE 0)
  {-@ body :: Btwn 1 40 ->
              {v:DSL _ (Btwn 0 40) | unpacked v} ->
              {v:DSL _ (Btwn 0 40) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int

-- (x0)^4 == 42
{-@ loop5 :: DSL _ (Btwn 0 20) @-}
loop5 :: DSL FF Int
loop5 = (ITER (B 2 4) body (WIRE 0)) `EQL` (CONST 42) where
  body = \_ p -> MUL p (WIRE 0)
  {-@ body :: Int ->
              {v:DSL _ (Btwn 0 20) | unpacked v} ->
              {v:DSL _ (Btwn 0 20) | unpacked v} @-}
  body :: Int -> DSL FF Int -> DSL FF Int

testLoops :: IO ()
testLoops = do
  test 20 loop1 (\case 0 -> 2; 1 -> 1; _ -> 0) -- 1 * 2^5 = 2^5  = 32
  test 20 loop1 (\case 0 -> 4; 1 -> 2; _ -> 0) -- 2 * 4^5 = 2^11 = 2048

  test 20 loop2 (const 0) -- 5! = 120
  test 20 loop3 (const 0) -- 1 + 2 + ... + 6 = 21

  -- decode 11111000 in binary (base x0 = 2) --> 248
  test 40 (loop4 8) (\i -> if i == 0 then 2
                           else if i > 8 then 0
                           else [1,1,1,1,1,0,0,0] !! (i-1))
  -- decode F8 in hexadecimal (base x0 = 16) --> 248
  test 40 (loop4 2) (\i -> if i == 0 then 16
                           else if i > 2 then 0
                           else [15, 8] !! (i-1))

  test 20 loop5 (const 627) -- 627^4 == 42 (mod 2131)

-- Vector programs -------------------------------------------------------------
{-@ vec1 :: {v:DSL _ (Btwn 0 20) | vlength v = 3} @-}
vec1 :: DSL FF Int
vec1 = (CONST 42)             `CONS`     -- 42
       (CONST 4 `SUB` WIRE 0) `CONS`     -- 4 - x_0
       (WIRE 1 `ADD` CONST 5) `CONS` NIL -- x_1 + 5

{-@ range :: lo:p -> hi:{p | hi >= lo} ->
             {res:DSL _ (Btwn 0 20) | isVector res && vlength res = hi-lo}
          / [hi-lo] @-}
range :: (Ord p, Num p) => p -> p -> DSL p Int
range a b = if a == b then NIL else CONST a `CONS` (range (a+1) b)

-- (range 1 5) but writing 42 in the 2nd position
{-@ vec2 :: DSL _ (Btwn 0 20) @-}
vec2 :: DSL FF Int
vec2 = set (range 1 5) 2 (CONST 42) where

-- 3rd position of (range 1 5)
{-@ vec3 :: DSL _ (Btwn 0 20) @-}
vec3 :: DSL FF Int
vec3 = get (range 1 5) 3 where

-- multiply two vectors component-wise
{-@ vecMul :: a:{DSL _ (Btwn 0 20) | isVector a} ->
              b:{DSL _ (Btwn 0 20) | isVector b && vlength b = vlength a} ->
              c:{DSL _ (Btwn 0 20) | isVector c && vlength c = vlength a} @-}
vecMul :: DSL FF Int -> DSL FF Int -> DSL FF Int
vecMul (NIL)       (NIL)       = NIL
vecMul (CONS a as) (CONS b bs) = CONS (MUL a b) (vecMul as bs)
-- vecMul = bitwise MUL
-- the inferred type ‘Int’ is not a subtype of the required type ‘Nat’

-- [1, 2, 3] * [5, 6, 7] = [1*5, 2*6, 3*7] = [5, 12, 21]
{-@ vec4 :: DSL _ (Btwn 0 20) @-}
vec4 :: DSL FF Int
vec4 = vecMul (range 1 4) (range 5 8)

{-@ vec5 :: {v:DSL _ (Btwn 0 20) | vlength v = 9} @-}
vec5 :: DSL FF Int
vec5 = rotateL (range 1 10) 3

{-@ vec6 :: {v:DSL _ (Btwn 0 20) | vlength v = 9} @-}
vec6 :: DSL FF Int
vec6 = rotateR (range 1 10) 2

{-@ vec7 :: {v:DSL _ (Btwn 0 500) | isVector v && vlength v >= 0} @-}
vec7 :: DSL FF Int
vec7 = vecAdd (PlinkLib.fromList [CONST 0, CONST 1, CONST 1]) -- 2
              (PlinkLib.fromList [CONST 0, CONST 1, CONST 0]) -- 3


testVectors :: IO ()
testVectors = do
  test 20 vec1 (\i -> if i < 2 then [1,2] !! i else 0)

  test 20 vec2 (const 0)
  test 20 vec3 (const 0)
  test 20 vec4 (const 0)

  test 20 vec5 (const 0)
  test 20 vec6 (const 0)

  test 500 vec7 (const 0)
