{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# OPTIONS -Wno-unused-imports #-}
{-# LANGUAGE DataKinds #-}

module Examples ( testArithmetic
                , testBoolean
                -- , testLoops
                , testVectors
                , testMod
                , testSha
                )
where

import GHC.TypeNats (KnownNat)
import Data.Char (ord)

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

import Treekz
import SHA256

import GlobalStore

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

{-@ test :: GlobalStore p (DSL p) -> Valuation p -> IO () @-}
test :: (Ord p, Fractional p, Show p) =>
        GlobalStore p (DSL p) -> Valuation p -> IO ()
test (GStore program store hints) valuation = do
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

  putStrLn $ replicate 80 '='


{-@ test' :: GlobalStore p (DSL p) -> Valuation p -> String -> IO () @-}
test' :: (Ord p, Fractional p, Show p) =>
         GlobalStore p (DSL p) -> Valuation p -> String -> IO ()
test' (GStore program store hints) valuation tikzFilename = do
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
  test (pure arith1) (M.fromList [("a",1), ("b",1), ("c",1), ("d",1)])
  test (pure arith2) (M.fromList [("a",7), ("b",3)])     -- (7+15) * (3+3) = 13
  test (pure arith3) (M.fromList [("num",3), ("den",9)]) -- 3 / 9          = 6

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
  test (pure bool1) (M.fromList [("a",0), ("b",3)]) -- a == 0
  test (pure bool1) (M.fromList [("a",1), ("b",0)]) -- a /= 0 && b == 0
  test (pure bool1) (M.fromList [("a",1), ("b",8)]) -- a /= 0 && b /= 0

  test (pure bool2) (M.fromList [("inv",5)]) -- 7 * 5 == 1 (== True)
  test (pure bool2) (M.fromList [("inv",7)]) -- 7 * 7 == 1 (== False)

  test (pure bool3) (M.fromList [("addsTo5",2)]) -- 2 + 2 == 5 (== False)
  test (pure bool3) (M.fromList [("addsTo5",3)]) -- 3 + 2 == 5 (== True)

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
--   test loop1 (M.fromList [("base",2), ("start",1)]) -- 1 * 2^5 = 2^5  = 32
--   test loop1 (M.fromList [("base",4), ("start",2)]) -- 2 * 4^5 = 2^11 = 2048

--   test loop2 (M.empty) -- 5! = 120
--   test loop3 (M.empty) -- 1 + 2 + ... + 6 = 21

--   let coefs = map (\n -> "coef" ++ show n) [1..]

--   -- decode 11111000 in binary (base x = 2) --> 248
--   test (loop4 8) (M.fromList $ [("x",2)] ++ zip coefs [1,1,1,1,1,0,0,0])
--   -- decode F8 in hexadecimal (base x = 16) --> 248
--   test (loop4 2) (M.fromList $ [("x",16)] ++ zip coefs [15, 8])

--   test loop5 (M.fromList [("base",627)]) -- 627^4 == 42 (mod 2131)

-- Vector programs -------------------------------------------------------------
{-@ vec1 :: {v:DSL _ | vlength v = 3} @-}
vec1 :: DSL PF
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
vec2 :: DSL PF
vec2 = set (range 1 5) 2 (CONST 42) where

-- 3rd position of (range 1 5)
{-@ vec3 :: DSL _ @-}
vec3 :: DSL PF
vec3 = get (range 1 5) 3 where

-- multiply two vectors component-wise
{-@ vecMul :: a:{DSL _ | isVector a} ->
              b:{DSL _ | isVector b && vlength b = vlength a} ->
              c:{DSL _ | isVector c && vlength c = vlength a} @-}
vecMul :: DSL PF -> DSL PF -> DSL PF
vecMul = vZipWith MUL

-- [1, 2, 3] * [5, 6, 7] = [1*5, 2*6, 3*7] = [5, 12, 21]
{-@ vec4 :: DSL _ @-}
vec4 :: DSL PF
vec4 = vecMul (range 1 4) (range 5 8)

{-@ vec5 :: {v:DSL _ | vlength v = 9} @-}
vec5 :: DSL PF
vec5 = rotateL (range 1 10) 3

{-@ vec6 :: {v:DSL _ | vlength v = 9} @-}
vec6 :: DSL PF
vec6 = rotateR (range 1 10) 2

-- {-@ vec7 :: GlobalStore (Assertion PF) (DSL PF) @-}
-- vec7 :: GlobalStore (Assertion PF) (DSL PF)
-- vec7 = vecAdd (fromInt 3 2) (fromInt 3 3) -- 2 + 3, using 3 bits

-- {-@ vec8 :: GlobalStore (Assertion PF) (DSL PF) @-}
-- vec8 :: GlobalStore (Assertion PF) (DSL PF)
-- vec8 = vecAdd (fromHex ['f', 'e']) (fromHex ['0', '5']) where

-- {-@ vec9 :: GlobalStore (Assertion PF) (DSL PF) @-}
-- vec9 :: GlobalStore (Assertion PF) (DSL PF)
-- vec9 = do
--   let v1 = fromHex ['1','8','9','4','b','1','3','f']
--   let v2 = fromHex ['c','a','f','9','1','9','5','e']
--   let v3 = fromHex ['1','8','9','4','1','9','5','e']
--   let v4 = fromHex ['c','a','f','9','b','1','3','f']
--   pure v1 >>= vecAdd v2 >>= vecAdd v3 >>= vecAdd v4

{-@ vec10 :: GlobalStore PF (DSL PF) @-}
vec10 :: GlobalStore PF (DSL PF)
vec10 = fromBinary $ PlinkLib.fromList $ map CONST [1,1,0,1]

testVectors :: IO ()
testVectors = do
  test (pure vec1) (M.fromList [("a",1), ("b",2)]) -- [42,3,7]

  test (pure vec2) M.empty -- [1,2,42,4]
  test (pure vec3) M.empty -- 4
  test (pure vec4) M.empty -- [5,12,21]

  test (pure vec5) M.empty -- [4,5,6,7,8,9,1,2,3]
  test (pure vec6) M.empty -- [8,9,1,2,3,4,5,6,7]

  -- test vec7 M.empty -- "treekz/test_addition.tex" -- [1,0,1]

  -- test vec8 M.empty

  -- test vec9 M.empty
  test vec10 M.empty

-- Modular arithmetic examples -------------------------------------------------

mod1 :: GlobalStore PF (DSL PF)
mod1 = addMod (CONST 32) (VAR "x") (VAR "y")


shift :: GlobalStore PF (DSL PF)
shift = do
  let x = VAR "x"
  vec <- toBinary 3 x
  y   <- fromBinary (shiftR vec 1)
  return y


rotate :: GlobalStore PF (DSL PF)
rotate = do
  let x = VAR "x"
  vec <- toBinary 5 x
  res <- fromBinary (rotateR vec 2)
  return res


testMod :: IO ()
testMod = do
  test mod1 (M.fromList [("x",27), ("y",3)]) -- 27 + 3 (mod 32) = 30
  test mod1 (M.fromList [("x",27), ("y",7)]) -- 27 + 7 (mod 32) = 2
  test shift (M.fromList [("x",5)])          -- 5 >> 1 = 2

  test rotate (M.fromList [("x", 11)]) -- 11 = 010|11 -> 11|010 = 26
  test rotate (M.fromList [("x", 15)]) -- 15 = 011|11 -> 11|011 = 27
  test rotate (M.fromList [("x", 13)]) -- 13 = 011|01 -> 01|011 = 11
  test rotate (M.fromList [("x",  6)]) --  6 = 001|10 -> 10|001 = 17

-- SHA256 examples -------------------------------------------------------------

{-@ assume ord :: Char -> Btwn 0 256 @-}

{-@ sha256 :: {s:String | len s < pow 2 61} ->
              GlobalStore p ({res:DSL p | isVector res}) @-}
sha256 :: (Integral p, Fractional p, Ord p) => String -> GlobalStore p (DSL p)
sha256 = processMsg . padding . toBits where
  {-@ toBits :: s:String
             -> {v:DSL p | isVector v && vlength v = 8 * len s} @-}
  toBits :: Num p => String -> DSL p
  toBits [] = NIL
  toBits (c:cs) = fromInt 8 (ord c) +++ toBits cs

sha256_1 :: GlobalStore BigPF (DSL BigPF)
sha256_1 = sha256 "Hello, world!"

sha256_2 :: GlobalStore BigPF (DSL BigPF)
sha256_2 = sha256 ""

sha256_3 :: GlobalStore BigPF (DSL BigPF)
sha256_3 = sha256 "The quick brown fox jumps over the lazy dog"



testSha :: IO ()
testSha = do
  test sha256_1 M.empty
  test sha256_2 M.empty
  test sha256_3 M.empty
