{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# OPTIONS -Wno-unused-imports #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module Examples ( testArithmetic
                , testBoolean
                , testLoops
                , testVectors
                , testLet
                )
where

import qualified Data.Map as M
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

import Treekz

type F p = PrimeField p
type F17 = F 17
type FF  = F 2131

-- Generic test function -------------------------------------------------------
cyan :: String -> String
cyan s = "\ESC[36m" ++ s ++ "\ESC[0m"

{-@ compose' :: m:Nat -> Env m -> M.Map String p -> M.Map (Btwn 0 m) p @-}
compose' :: Int -> Env -> M.Map String p -> M.Map Int p
compose' _ env val = M.compose val (invert env) where
  invert = M.fromList . map swap . M.toList
  swap (a,b) = (b,a)
  invert :: M.Map String Int -> M.Map Int String
  swap :: (String, Int) -> (Int, String)


{-@ test :: DSL _ -> (M.Map String p) -> IO () @-}
test :: (Eq p, Fractional p, Show p) =>
        DSL p -> (M.Map String p) -> IO ()
test program valuation = do
  let desugaredProgram = desugar program
  let m = 1 + nWires desugaredProgram -- upper bound for #(needed wires)
  let (bodies, bindings, env) = label m [desugaredProgram]
  let labeledPrograms = bindings ++ bodies

  let circuit = concatMap (compile m) labeledPrograms
  let input = witnessGen m labeledPrograms (compose' m env valuation)
  let output = map (\p -> input ! outputWire p) bodies

  putStrLn $ "Preprocessed program: " ++ show labeledPrograms
  putStrLn $ "Compiled circuit:     " ++ show circuit
  putStrLn $ "Input:                " ++ show input
  putStrLn $ "Final result: " ++ cyan (show output)

  putStrLn $ replicate 80 '='


{-@ test' :: DSL _ -> (M.Map String p) -> String -> IO () @-}
test' :: (Eq p, Fractional p, Show p) =>
         DSL p -> (M.Map String p) -> String -> IO ()
test' program valuation tikzFilename = do
  let desugaredProgram = desugar program
  let m = 1 + nWires desugaredProgram -- upper bound for #(needed wires)
  let (bodies, bindings, env) = label m [desugaredProgram]
  let labeledPrograms = bindings ++ bodies

  let circuit = concatMap (compile m) labeledPrograms
  let input = witnessGen m labeledPrograms (compose' m env valuation)
  let output = map (\p -> input ! outputWire p) bodies

  putStrLn $ "Preprocessed program: " ++ show labeledPrograms
  putStrLn $ "Compiled circuit:     " ++ show circuit
  putStrLn $ "Input:                " ++ show input
  putStrLn $ "Variable environment: " ++ show env
  putStrLn $ "Final result: " ++ cyan (show output)

  let treekzCode = map parse labeledPrograms
  let tikzStr = genTikzs 0.45 (14, -1.5) treekzCode
  writeFile tikzFilename (intro ++ tikzStr ++ outro)

  putStrLn $ replicate 80 '='

-- Arithmetic programs ---------------------------------------------------------
-- (a + b) + (c + d)
{-@ arith1 :: v:DSL _ @-}
arith1 :: DSL F17
arith1 = ADD (ADD (VAR "a") (VAR "b")) (ADD (VAR "c") (VAR "d"))

-- (a + 15) * (b + 3)
{-@ arith2 :: v:DSL _ @-}
arith2 :: DSL F17
arith2 = MUL (ADD (VAR "a") (CONST 15)) (ADD (VAR "b") (CONST 3))

-- num / den
{-@ arith3 :: DSL _ @-}
arith3 :: DSL F17
arith3 = DIV (VAR "num") (VAR "den")

testArithmetic :: IO ()
testArithmetic = do
  -- (1+1)  + (1+1) = 4
  test arith1 (M.fromList [("a",1), ("b",1), ("c",1), ("d",1)])
  test arith2 (M.fromList [("a",7), ("b",3)])     -- (7+15) * (3+3) = 13
  test arith3 (M.fromList [("num",3), ("den",9)]) -- 3 / 9          = 6

-- Boolean programs ------------------------------------------------------------
-- a == 0 || (a /= 0 && b == 1)
{-@ bool1 :: DSL _ @-}
bool1 :: DSL F17
bool1 = ISZERO (VAR "a") `OR` (NOT (ISZERO (VAR "a")) `AND` (ISZERO (VAR "b")))

-- 7 * inv == 1
{-@ bool2 :: DSL _ @-}
bool2 :: DSL F17
bool2 = (CONST 7 `MUL` VAR "inv") `EQL` CONST 1

-- addTo5 + 2 == 5
{-@ bool3 :: DSL _ @-}
bool3 :: DSL F17
bool3 = (VAR "addsTo5" `ADD` CONST 2) `EQL` CONST 5

testBoolean :: IO ()
testBoolean = do
  test bool1 (M.fromList [("a",0), ("b",3)]) -- a == 0
  test bool1 (M.fromList [("a",1), ("b",0)]) -- a /= 0 && b == 0
  test bool1 (M.fromList [("a",1), ("b",8)]) -- a /= 0 && b /= 0

  test bool2 (M.fromList [("inv",5)]) -- 7 * 5 == 1 (== True)
  test bool2 (M.fromList [("inv",7)]) -- 7 * 7 == 1 (== False)

  test bool3 (M.fromList [("addsTo5",2)]) -- 2 + 2 == 5 (== False)
  test bool3 (M.fromList [("addsTo5",3)]) -- 3 + 2 == 5 (== True)

-- Loop programs ---------------------------------------------------------------
-- start * (base)^5
{-@ loop1 :: DSL _ @-}
loop1 :: DSL FF
loop1 = ITER (B 1 5) body (VAR "start") where
  {-@ body :: Int ->
              {v:DSL _ | unpacked v} ->
              {v:DSL _ | unpacked v} @-}
  body :: Int -> DSL FF -> DSL FF
  body = (\_ p -> MUL p (VAR "base"))

-- 5! = 120
{-@ loop2 :: DSL _ @-}
loop2 :: DSL FF
loop2 = ITER (B 2 5) body (CONST 1) where
  {-@ body :: Int ->
              {v:DSL _ | unpacked v} ->
              {v:DSL _ | unpacked v} @-}
  body :: Int -> DSL FF -> DSL FF
  body = \i p -> MUL p (CONST $ fromIntegral i)

-- 1 + 2 + 3 + 4 + 5 + 6 = 21
{-@ loop3 :: DSL _ @-}
loop3 :: DSL FF
loop3 = ITER (B 1 6) body (CONST 0) where
  {-@ body :: Int ->
              {v:DSL _ | unpacked v} ->
              {v:DSL _ | unpacked v} @-}
  body :: Int -> DSL FF -> DSL FF
  body = \i p -> ADD p (CONST $ fromIntegral i)

-- Polynomial evaluation:
-- x_1 * x^(n-1) + x_2 * x^(n-2) + ... + x_(n-1) * x + x_n
{-@ loop4 :: Btwn 1 39 -> DSL _ @-}
loop4 :: Int -> DSL FF
loop4 n = ITER (B 1 n) body (CONST 0) where
  body = \i p -> (VAR $ "coef" ++ show i) `ADD` (p `MUL` VAR "x") --FIXME:
  {-@ body :: Btwn 1 40 ->
              {v:DSL _ | unpacked v} ->
              {v:DSL _ | unpacked v} @-}
  body :: Int -> DSL FF -> DSL FF

-- (base)^4 == 42
{-@ loop5 :: DSL _ @-}
loop5 :: DSL FF
loop5 = (ITER (B 2 4) body (VAR "base")) `EQL` (CONST 42) where
  body = \_ p -> MUL p (VAR "base")
  {-@ body :: Int ->
              {v:DSL _ | unpacked v} ->
              {v:DSL _ | unpacked v} @-}
  body :: Int -> DSL FF -> DSL FF

testLoops :: IO ()
testLoops = do
  test loop1 (M.fromList [("base",2), ("start",1)]) -- 1 * 2^5 = 2^5  = 32
  test loop1 (M.fromList [("base",4), ("start",2)]) -- 2 * 4^5 = 2^11 = 2048

  test loop2 (M.empty) -- 5! = 120
  test loop3 (M.empty) -- 1 + 2 + ... + 6 = 21

  let coefs = map (\n -> "coef" ++ show n) [1..]

  -- decode 11111000 in binary (base x = 2) --> 248
  test (loop4 8) (M.fromList $ [("x",2)] ++ zip coefs [1,1,1,1,1,0,0,0])
  -- decode F8 in hexadecimal (base x = 16) --> 248
  test (loop4 2) (M.fromList $ [("x",16)] ++ zip coefs [15, 8])

  test loop5 (M.fromList [("base",627)]) -- 627^4 == 42 (mod 2131)

-- Vector programs -------------------------------------------------------------
{-@ vec1 :: {v:DSL _ | vlength v = 3} @-}
vec1 :: DSL FF
vec1 = (CONST 42)             `CONS`      -- 42
       (CONST 4 `SUB` VAR "a") `CONS`     -- 4 - a
       (VAR "b" `ADD` CONST 5) `CONS` NIL -- b + 5

{-@ range :: lo:p -> hi:{p | hi >= lo} ->
             {res:DSL _ | isVector res && vlength res = hi-lo}
          / [hi-lo] @-}
range :: (Ord p, Num p) => p -> p -> DSL p
range a b = if a == b then NIL else CONST a `CONS` (range (a+1) b)

-- (range 1 5) but writing 42 in the 2nd position
{-@ vec2 :: DSL _ @-}
vec2 :: DSL FF
vec2 = set (range 1 5) 2 (CONST 42) where

-- 3rd position of (range 1 5)
{-@ vec3 :: DSL _ @-}
vec3 :: DSL FF
vec3 = get (range 1 5) 3 where

-- multiply two vectors component-wise
{-@ vecMul :: a:{DSL _ | isVector a} ->
              b:{DSL _ | isVector b && vlength b = vlength a} ->
              c:{DSL _ | isVector c && vlength c = vlength a} @-}
vecMul :: DSL FF -> DSL FF -> DSL FF
vecMul = vZipWith MUL

-- [1, 2, 3] * [5, 6, 7] = [1*5, 2*6, 3*7] = [5, 12, 21]
{-@ vec4 :: DSL _ @-}
vec4 :: DSL FF
vec4 = vecMul (range 1 4) (range 5 8)

{-@ vec5 :: {v:DSL _ | vlength v = 9} @-}
vec5 :: DSL FF
vec5 = rotateL (range 1 10) 3

{-@ vec6 :: {v:DSL _ | vlength v = 9} @-}
vec6 :: DSL FF
vec6 = rotateR (range 1 10) 2

vec7 :: DSL FF
vec7 = vecAdd (fromInt 3 2) (fromInt 3 3) -- 2 + 3, using 3 bits

vec8 :: DSL FF
vec8 = vecAdd (fromHex ['a', '4']) (fromHex ['4', 'b']) where

testVectors :: IO ()
testVectors = do
  test vec1 (M.fromList [("a",1), ("b",2)])

  test vec2 (M.empty)
  test vec3 (M.empty)
  test vec4 (M.empty)

  test vec5 (M.empty)
  test vec6 (M.empty)

  test' vec7 (M.empty) "treekz/int_addition.tex"
  test vec8 (M.empty)


-- Local bindings --------------------------------------------------------------

-- let x = 5 in let y = 7 in x + y
let1 :: DSL FF
let1 = LET "x" (CONST 5) (LET "y" (CONST 7) (VAR "x" `ADD` VAR "y"))

-- let x = 5 in let x = 7 in x
let2 :: DSL FF
let2 = LET "x" (CONST 5) (LET "x" (CONST 7) (VAR "x"))

-- let x = 2 in (let x = 1 in x) + x
let3 :: DSL FF
let3 = LET "x" (CONST 2) ((LET "x" (CONST 1) (VAR "x")) `ADD` (VAR "x"))

testLet :: IO ()
testLet = do
  test let1 (M.empty) -- 12
  test let2 (M.empty) -- 7
  test let3 (M.empty) -- 3
