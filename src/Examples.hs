{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-# OPTIONS -Wno-unused-imports #-}
{-# LANGUAGE DataKinds #-}

module Examples ( testArithmetic
                , testBoolean
                -- , testLoops
                , testVectors
                , testMod
                , testSha
                , testOpt
                )
where

import GHC.TypeNats (KnownNat)

import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.FiniteField.PrimeField
import qualified Data.FiniteField.PrimeField as PF (toInteger)
import Vec
import PlinkLib

import Utils           -- needed to use reflected functions
import Circuits        -- needed to use reflected functions
import ArithmeticGates -- needed to use reflected functions
import LogicGates      -- needed to use reflected functions

import Constraints

import DSL
import Label
import WitnessGeneration
import Optimizations

import Treekz
import SHA256

import GlobalStore

import Language.Haskell.Liquid.ProofCombinators

type F p = PrimeField p
type F17 = F 17
type PF  = F 2131
type BigPF = F 65454111407

-- Arguably sketchy instances for using `mod' ----------------------------------
instance KnownNat p => Real (PrimeField p) where
  toRational = toRational . PF.toInteger

instance KnownNat p => Integral (PrimeField p) where
  toInteger = PF.toInteger
  quot = wrapper quot
  rem = wrapper rem
  div = wrapper div
  mod = wrapper mod
  quotRem x y = (wrapper quot x y, wrapper rem x y)
  divMod x y = (wrapper div x y, wrapper mod x y)

{-@ wrapper :: (Integer -> {y:Integer | y /= 0} -> Integer)
            -> (PrimeField p -> PrimeField p -> PrimeField p) @-}
wrapper :: KnownNat p
        => (Integer -> Integer -> Integer)
        -> (PrimeField p -> PrimeField p -> PrimeField p)
wrapper op x y = do
  let x' = PF.toInteger x
  let y' = PF.toInteger y
  {-@ assume y' :: {v:_ | v /= 0} @-}
  fromInteger (x' `op` y')
--------------------------------------------------------------------------------

-- Generic test function -------------------------------------------------------
cyan :: String -> String
cyan s = "\ESC[36m" ++ s ++ "\ESC[0m"

nub :: Ord a => [a] -> [a]
nub = S.toList . S.fromList

{-@ test :: GlobalStore p (TypedDSL p) -> ValuationRefl p -> IO () @-}
test :: (Ord p, Fractional p, Show p) =>
        GlobalStore p (DSL p) -> ValuationRefl p -> IO ()
test programStore valuation = do
  let (GStore program store hints) = optimize programStore

  let valuation' = extend valuation hints

  -- let program' = constantFolding program
  let program' = program
  -- let store' = mapMaybe constantFolding' store
  let store' = store

  let (m, labeledBodies, labeledStore) = label program' store'
  let labeledPrograms = labeledStore ++ labeledBodies

  let circuit = concatMap (compile m) labeledPrograms

  let input = witnessGen m labeledPrograms valuation'
  let output = map (\p -> input ! outputWire p) labeledBodies
  let output' = map (\p -> input ! outputWire p) labeledStore

  -- putStrLn $ "Program (after optimizations):   " ++ show program' ++ ", " ++ show store'
  -- putStrLn $ "Preprocessed program: " ++ show labeledPrograms
  -- putStrLn $ "Compiled circuit: " ++ show circuit
  putStrLn $ "Compiled circuit has " ++ cyan (show $ length circuit) ++ " constraints"
  -- putStrLn $ "Input:                " ++ show input
  -- putStrLn $ "Auxiliary values:     " ++ cyan (show output')
  putStrLn $ "Final result: " ++ cyan (show output)

  putStrLn $ replicate 80 '='


{-@ test' :: GlobalStore p (TypedDSL p) -> ValuationRefl p -> String -> IO () @-}
test' :: (Ord p, Fractional p, Show p) =>
         GlobalStore p (DSL p) -> ValuationRefl p -> String -> IO ()
test' programStore valuation tikzFilename = do
  let (GStore program store hints) = optimize programStore

  let valuation' = extend valuation hints

  let (m, labeledBodies, labeledStore) = label program store
  let labeledPrograms = labeledStore ++ labeledBodies

  let circuit = concatMap (compile m) labeledPrograms
  let input = witnessGen m labeledPrograms valuation'
  let output = map (\p -> input ! outputWire p) labeledBodies
  let output' = map (\p -> input ! outputWire p) labeledStore

  -- putStrLn $ "Preprocessed program: " ++ show labeledPrograms
  putStrLn $ "Compiled circuit has " ++ cyan (show $ length circuit) ++ " constraints"
  -- putStrLn $ "Input:                " ++ show input
  -- putStrLn $ "Auxiliary values:     " ++ cyan (show output')
  putStrLn $ "Final result: " ++ cyan (show output)

  let treekzCode = map parse labeledPrograms
  let tikzStr = genTikzs 0.45 (14, -1.5) treekzCode
  writeFile tikzFilename (intro ++ tikzStr ++ outro)

  putStrLn $ replicate 80 '='

-- Arithmetic programs ---------------------------------------------------------
-- (a + b) + (c + d)
{-@ arith1 :: {v:DSL F17 | typed v TF} @-}
arith1 :: DSL F17
arith1 = ADD (ADD (VAR "a" TF) (VAR "b" TF)) (ADD (VAR "c" TF) (VAR "d" TF))

-- (a + 15) * (b + 3)
{-@ arith2 :: {v:DSL F17 | typed v TF} @-}
arith2 :: DSL F17
arith2 = MUL (ADD (VAR "a" TF) (CONST 15)) (ADD (VAR "b" TF) (CONST 3))

-- num / den
{-@ arith3 :: {v:DSL F17 | typed v TF} @-}
arith3 :: DSL F17
arith3 = DIV (VAR "num" TF) (VAR "den" TF)

testArithmetic :: IO ()
testArithmetic = do
  -- (1+1)  + (1+1) = 4
  test (pure arith1) ([("a",1), ("b",1), ("c",1), ("d",1)])
  test (pure arith2) ([("a",7), ("b",3)])     -- (7+15) * (3+3) = 13
  test (pure arith3) ([("num",3), ("den",9)]) -- 3 / 9          = 6

-- Boolean programs ------------------------------------------------------------
-- a == 0 || (a /= 0 && b == 1)
{-@ bool1 :: {v:DSL F17 | typed v TBool} @-}
bool1 :: DSL F17
bool1 = ISZERO (VAR "a" TF) `OR`
        (NOT (ISZERO (VAR "a" TF)) `AND` (ISZERO (VAR "b" TF)))

-- 7 * inv == 1
{-@ bool2 :: {v:DSL F17 | typed v TBool} @-}
bool2 :: DSL F17
bool2 = (CONST 7 `MUL` VAR "inv" TF) `EQL` CONST 1

-- addTo5 + 2 == 5
{-@ bool3 :: {v:DSL F17 | typed v TBool} @-}
bool3 :: DSL F17
bool3 = (VAR "addsTo5" TF `ADD` CONST 2) `EQL` CONST 5

testBoolean :: IO ()
testBoolean = do
  test (pure bool1) ([("a",0), ("b",3)]) -- a == 0
  test (pure bool1) ([("a",1), ("b",0)]) -- a /= 0 && b == 0
  test (pure bool1) ([("a",1), ("b",8)]) -- a /= 0 && b /= 0

  test (pure bool2) ([("inv",5)]) -- 7 * 5 == 1 (== True)
  test (pure bool2) ([("inv",7)]) -- 7 * 7 == 1 (== False)

  test (pure bool3) ([("addsTo5",2)]) -- 2 + 2 == 5 (== False)
  test (pure bool3) ([("addsTo5",3)]) -- 3 + 2 == 5 (== True)

-- Loop programs ---------------------------------------------------------------
-- -- start * (base)^5
-- {-@ loop1 :: DSL _ @-}
-- loop1 :: DSL PF
-- loop1 = foldl body (VAR "start") [1..5] where
--   {-@ body :: {v:DSL _ | unpacked v} ->
--               Int ->
--               {v:DSL _ | unpacked v} @-}
--   body :: DSL PF -> Int -> DSL PF
--   body = (\p _ -> MUL p (VAR "base"))

-- -- 5! = 120
-- {-@ loop2 :: DSL _ @-}
-- loop2 :: DSL PF
-- loop2 = foldl body (CONST 1) [2..5] where
--   {-@ body :: {v:DSL _ | unpacked v} ->
--               Int ->
--               {v:DSL _ | unpacked v} @-}
--   body :: DSL PF -> Int -> DSL PF
--   body = \p i -> MUL p (CONST $ fromIntegral i)

-- -- 1 + 2 + 3 + 4 + 5 + 6 = 21
-- {-@ loop3 :: DSL _ @-}
-- loop3 :: DSL PF
-- loop3 = foldl body (CONST 0) [1..6] where
--   {-@ body :: {v:DSL _ | unpacked v} ->
--               Int ->
--               {v:DSL _ | unpacked v} @-}
--   body :: DSL PF -> Int -> DSL PF
--   body = \p i -> ADD p (CONST $ fromIntegral i)

-- -- Polynomial evaluation:
-- -- x_1 * x^(n-1) + x_2 * x^(n-2) + ... + x_(n-1) * x + x_n
-- {-@ loop4 :: Btwn 1 39 -> DSL _ @-}
-- loop4 :: Int -> DSL PF
-- loop4 n = foldl body (CONST 0) [1..n] where
--   body = \p i -> (VAR $ "coef" ++ show i) `ADD` (p `MUL` VAR "x") --FIXME:
--   {-@ body :: {v:DSL _ | unpacked v} ->
--               Btwn 1 40 ->
--               {v:DSL _ | unpacked v} @-}
--   body :: DSL PF -> Int -> DSL PF

-- -- (base)^4 == 42
-- {-@ loop5 :: DSL _ @-}
-- loop5 :: DSL PF
-- loop5 = (foldl body (VAR "base") [2..4]) `EQL` (CONST 42) where
--   body = \p _ -> MUL p (VAR "base")
--   {-@ body :: {v:DSL _ | unpacked v} ->
--               Int ->
--               {v:DSL _ | unpacked v} @-}
--   body :: DSL PF -> Int -> DSL PF

-- testLoops :: IO ()
-- testLoops = do
--   test loop1 ([("base",2), ("start",1)]) -- 1 * 2^5 = 2^5  = 32
--   test loop1 ([("base",4), ("start",2)]) -- 2 * 4^5 = 2^11 = 2048

--   test loop2 ([]) -- 5! = 120
--   test loop3 ([]) -- 1 + 2 + ... + 6 = 21

--   let coefs = map (\n -> "coef" ++ show n) [1..]

--   -- decode 11111000 in binary (base x = 2) --> 248
--   test (loop4 8) ([("x",2)] ++ zip coefs [1,1,1,1,1,0,0,0])
--   -- decode F8 in hexadecimal (base x = 16) --> 248
--   test (loop4 2) ([("x",16)] ++ zip coefs [15, 8])

--   test loop5 ([("base",627)]) -- 627^4 == 42 (mod 2131)

-- Vector programs -------------------------------------------------------------
{-@ vec1 :: {v:DSL PF | typed v (TVec TF 3)} @-}
vec1 :: DSL PF
vec1 = (CONST 42)                    `CONS`        -- 42
       (CONST 4    `SUB` VAR "a" TF) `CONS`        -- 4 - a
       (VAR "b" TF `ADD` CONST 5)    `CONS` NIL TF -- b + 5

{-@ range :: lo:p -> hi:{p | hi >= lo} ->
             {res:DSL p | typed res (TVec TF (hi-lo))}
          / [hi-lo] @-}
range :: (Ord p, Num p) => p -> p -> DSL p
range a b = if a == b then NIL TF else CONST a `CONS` (range (a+1) b)

{-@ lenThm :: τ:Ty -> n:Nat
           -> v:{DSL p | typed v (TVec τ n)}
           -> {vlength v = n} @-}
lenThm :: Ty -> Int -> DSL p -> Proof
lenThm τ n v = case v of
  NIL  _    -> trivial
  CONS _ xs -> lenThm τ (n-1) xs
  VAR  _ _  -> trivial

-- (range 1 5) but writing 42 in the 2nd position
{-@ vec2 :: {v:DSL PF | typed v (TVec TF 4)} @-}
vec2 :: DSL PF
vec2 = lenThm TF 4 (range 1 5) ?? set TF (range 1 5) 2 (CONST 42)

-- 3rd position of (range 1 5)
{-@ vec3 :: {v:DSL PF | typed v TF} @-}
vec3 :: DSL PF
vec3 = lenThm TF 4 (range 1 5) ?? get TF (range 1 5) 3 where

-- multiply two vectors component-wise
{-@ vecMul :: a:PlinkVec p TF ->
              b:{PlinkVec p TF | vlength b = vlength a} ->
              c:{PlinkVec p TF | vlength c = vlength a} @-}
vecMul :: DSL p -> DSL p -> DSL p
vecMul = vZipWith TF TF TF MUL

-- [1, 2, 3] * [5, 6, 7] = [1*5, 2*6, 3*7] = [5, 12, 21]
{-@ vec4 :: {v:DSL PF | typed v (TVec TF 3)} @-}
vec4 :: DSL PF
vec4 = let v = (range 1 4); w = (range 5 8)
  in lenThm TF 3 v ?? lenThm TF 3 w ?? vecMul v w

{-@ vec5 :: {v:DSL PF | typed v (TVec TF 9)} @-}
vec5 :: DSL PF
vec5 = lenThm TF 9 (range 1 10) ?? rotateL TF (range 1 10) 3

{-@ vec6 :: {v:DSL PF | typed v (TVec TF 9)} @-}
vec6 :: DSL PF
vec6 = lenThm TF 9 (range 1 10) ?? rotateR TF (range 1 10) 2

{-@ vec7 :: GlobalStore PF ({v:DSL PF | typed v TF}) @-}
vec7 :: GlobalStore PF (DSL PF)
vec7 = fromBinary $ PlinkLib.fromList TBool $ map boolFromIntegral [1,1,0,1]

testVectors :: IO ()
testVectors = do
  test (pure vec1) ([("a",1), ("b",2)]) -- [42,3,7]

  test (pure vec2) [] -- [1,2,42,4]
  test (pure vec3) [] -- 4
  test (pure vec4) [] -- [5,12,21]

  test (pure vec5) [] -- [4,5,6,7,8,9,1,2,3]
  test (pure vec6) [] -- [8,9,1,2,3,4,5,6,7]

  test vec7 [] -- 0b1101 = 13

-- Modular arithmetic examples -------------------------------------------------

{-@ mod1 :: GlobalStore PF ({v:DSL PF | typed v TF}) @-}
mod1 :: GlobalStore PF (DSL PF)
mod1 = addMod 5 (VAR "x" TF) (VAR "y" TF)


{-@ shift :: GlobalStore PF ({v:DSL PF | typed v TF}) @-}
shift :: GlobalStore PF (DSL PF)
shift = do
  let x = VAR "x" TF
  vec <- toBinary 3 x
  y   <- fromBinary (shiftR vec 1)
  return y


{-@ rotate :: GlobalStore PF ({v:DSL PF | typed v TF}) @-}
rotate :: GlobalStore PF (DSL PF)
rotate = do
  let x = VAR "x" TF
  vec <- toBinary 5 x
  res <- binaryValue (rotateR TBool vec 2)
  return res


testMod :: IO ()
testMod = do
  test mod1 ([("x",27), ("y",3)]) -- 27 + 3 (mod 32) = 30
  test mod1 ([("x",27), ("y",7)]) -- 27 + 7 (mod 32) = 2
  test shift ([("x",5)])          -- 5 >> 1 = 2

  test rotate ([("x", 11)]) -- 11 = 010|11 -> 11|010 = 26
  test rotate ([("x", 15)]) -- 15 = 011|11 -> 11|011 = 27
  test rotate ([("x", 13)]) -- 13 = 011|01 -> 01|011 = 11
  test rotate ([("x",  6)]) --  6 = 001|10 -> 10|001 = 17

-- SHA256 examples -------------------------------------------------------------

{-@ sha256_1 :: GlobalStore BigPF (PlinkVec BigPF TBool) @-}
sha256_1 :: GlobalStore BigPF (DSL BigPF)
sha256_1 = sha256 "Hello, world!"

{-@ sha256_2 :: GlobalStore BigPF (PlinkVec BigPF TBool) @-}
sha256_2 :: GlobalStore BigPF (DSL BigPF)
sha256_2 = sha256 ""

{-@ sha256_3 :: GlobalStore BigPF (PlinkVec BigPF TBool) @-}
sha256_3 :: GlobalStore BigPF (DSL BigPF)
sha256_3 = sha256 "The quick brown fox jumps over the lazy dog"

{-@ sha256_4 :: GlobalStore BigPF (PlinkVec BigPF TBool) @-}
sha256_4 :: GlobalStore BigPF (DSL BigPF)
sha256_4 = sha256 (replicate 64 'a')

{-@ sha256_5 :: GlobalStore BigPF (PlinkVec BigPF TBool) @-}
sha256_5 :: GlobalStore BigPF (DSL BigPF)
sha256_5 = sha256 (replicate (2*64) 'a')

{-@ sha256_6 :: GlobalStore BigPF (PlinkVec BigPF TBool) @-}
sha256_6 :: GlobalStore BigPF (DSL BigPF)
sha256_6 = sha256 (replicate (3*64) 'a')

{-@ sha256_7 :: GlobalStore BigPF (PlinkVec BigPF TBool) @-}
sha256_7 :: GlobalStore BigPF (DSL BigPF)
sha256_7 = sha256 (replicate (4*64) 'a')

testSha :: IO ()
testSha = do
  test sha256_1 []
  -- test sha256_2 []
  -- test sha256_3 []
  -- test sha256_4 []
  -- test sha256_5 []
  -- test sha256_6 []
  -- test sha256_7 []

-- Optimizations ---------------------------------------------------------------

-- (3 - (2 + 1)) + x ≡ x
{-@ opt1 :: GlobalStore BigPF ({v:DSL BigPF | typed v TF}) @-}
opt1 :: GlobalStore BigPF (DSL BigPF)
opt1 = let p = (CONST 3 `SUB` (CONST 2 `ADD` CONST 1)) `ADD` (VAR "x" TF)
       in inferType p ?? pure p

-- (3 - 2) * x + y ≡ x + y
{-@ opt2 :: GlobalStore BigPF ({v:DSL BigPF | typed v TF}) @-}
opt2 :: GlobalStore BigPF (DSL BigPF)
opt2 = let p = ((CONST 3 `SUB` CONST 2) `MUL` (VAR "x" TF)) `ADD` (VAR "y" TF)
       in inferType p ?? pure p

-- (3 - 1) * x + y ≡ lincomb(2,x, 1,y)
{-@ opt3 :: GlobalStore BigPF ({v:DSL BigPF | typed v TF}) @-}
opt3 :: GlobalStore BigPF (DSL BigPF)
opt3 = let p = ((CONST 3 `SUB` CONST 1) `MUL` (VAR "x" TF)) `ADD` (VAR "y" TF)
       in inferType p ?? pure p

testOpt :: IO ()
testOpt = do
  test opt1 ([("x",7), ("y",2)])
  test opt2 ([("x",7), ("y",2)])
  test opt3 ([("x",7), ("y",2)])
