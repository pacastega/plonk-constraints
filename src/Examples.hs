{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-# OPTIONS -Wno-unused-imports #-}
{-# LANGUAGE DataKinds, CPP #-}

module Examples ( testArithmetic
                , testBoolean
                -- , testLoops
                , testVectors
                , testMod
                , testSha
                , testPoseidon
                , testOpt
                )
where

import GHC.TypeNats (KnownNat)

import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import Data.FiniteField.PrimeField
import qualified Data.FiniteField.PrimeField as PF (toInteger)
import Vec
import PlinkLib

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

import Utils           -- needed to use reflected functions
import Circuits        -- needed to use reflected functions
import ArithmeticGates -- needed to use reflected functions
import LogicGates      -- needed to use reflected functions

import Constraints

import DSL
import Label
import WitnessGeneration
import Optimizations
import Semantics (NameValuation)

import Treekz
import SHA256
import Poseidon2.Poseidon2Cnst
import Poseidon2.Poseidon2

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


-- Workaround to fix "crash: unknown constant" ---------------------------------
{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
--------------------------------------------------------------------------------


-- Generic test function -------------------------------------------------------
cyan :: String -> String
cyan s = "\ESC[36m" ++ s ++ "\ESC[0m"

nub :: Ord a => [a] -> [a]
nub = S.toList . S.fromList

{-@ test :: GlobalStore p (TypedDSL p) -> NameValuation p -> IO () @-}
test :: (Ord p, Fractional p, Show p) =>
        GlobalStore p (DSL p) -> NameValuation p -> IO ()
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

  -- putStrLn $ "Program (after optimizations):   " ++ show program' ++ ", " ++ show store'
  -- putStrLn $ "Preprocessed program: " ++ show labeledPrograms
  -- putStrLn $ "Compiled circuit: " ++ show circuit
  putStrLn $ "Compiled circuit has " ++ cyan (show $ length circuit) ++ " constraints"

  case witnessGen m labeledPrograms valuation' of
    Nothing -> do putStrLn "Witness generation failed"
                  putStrLn $ replicate 80 '='
    Just input -> do
      let output = map (\p -> input ! outputWire p) labeledBodies
      let output' = map (\p -> input ! outputWire p) labeledStore

      -- putStrLn $ "Input:                " ++ show input
      -- putStrLn $ "Auxiliary values:     " ++ cyan (show output')
      putStrLn $ "Final result: " ++ cyan (show output)

      putStrLn $ replicate 80 '='


{-@ test' :: GlobalStore p (TypedDSL p) -> NameValuation p -> String -> IO () @-}
test' :: (Ord p, Fractional p, Show p) =>
         GlobalStore p (DSL p) -> NameValuation p -> String -> IO ()
test' programStore valuation tikzFilename = do
  let (GStore program store hints) = optimize programStore

  let valuation' = extend valuation hints

  let (m, labeledBodies, labeledStore) = label program store
  let labeledPrograms = labeledStore ++ labeledBodies

  let circuit = concatMap (compile m) labeledPrograms
  case witnessGen m labeledPrograms valuation' of
    Nothing -> putStrLn "Witness generation failed"
    Just input -> do
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
{-@ arith1 :: FieldDSL F17 @-}
arith1 :: DSL F17
arith1 = (VAR "a" TF `plus` VAR "b" TF) `plus` (VAR "c" TF `plus` VAR "d" TF)

-- (a + 15) * (b + 3)
{-@ arith2 :: FieldDSL F17 @-}
arith2 :: DSL F17
arith2 = (VAR "a" TF `plus` CONST 15) `times` (VAR "b" TF `plus` CONST 3)

-- num / den
{-@ arith3 :: FieldDSL F17 @-}
arith3 :: DSL F17
arith3 = VAR "num" TF `over` VAR "den" TF

testArithmetic :: IO ()
testArithmetic = do
  -- (1+1)  + (1+1) = 4
  test (pure arith1) (M.fromList [("a",1), ("b",1), ("c",1), ("d",1)])
  test (pure arith2) (M.fromList [("a",7), ("b",3)])     -- (7+15) * (3+3) = 13
  test (pure arith3) (M.fromList [("num",3), ("den",9)]) -- 3 / 9          = 6

-- Boolean programs ------------------------------------------------------------
-- a == 0 || (a /= 0 && b == 1)
{-@ bool1 :: BoolDSL F17 @-}
bool1 :: DSL F17
bool1 = UN ISZERO (VAR "a" TF) \/
        ((UN NOT (UN ISZERO (VAR "a" TF))) /\ (UN ISZERO (VAR "b" TF)))

-- 7 * inv == 1
{-@ bool2 :: BoolDSL F17 @-}
bool2 :: DSL F17
bool2 = (CONST 7 `times` VAR "inv" TF) =? CONST 1

-- addTo5 + 2 == 5
{-@ bool3 :: BoolDSL F17 @-}
bool3 :: DSL F17
bool3 = (VAR "addsTo5" TF `plus` CONST 2) =? CONST 5

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
{-@ vec1 :: VecDSL PF TF @-}
vec1 :: DSL PF
vec1 = (CONST 42)                      `CONS`        -- 42
       (CONST 4    `minus` VAR "a" TF) `CONS`        -- 4 - a
       (VAR "b" TF `plus`  CONST 5)    `CONS` NIL TF -- b + 5

{-@ range :: lo:p -> hi:{p | hi >= lo} ->
             {res:VecDSL p TF | vlength res == (hi-lo)}
          / [hi-lo] @-}
range :: (Ord p, Num p) => p -> p -> DSL p
range a b = if a == b then NIL TF else CONST a `CONS` (range (a+1) b)

-- (range 1 5) but writing 42 in the 2nd position
{-@ vec2 :: VecDSL PF TF @-}
vec2 :: DSL PF
vec2 = set TF (range 1 5) 2 (CONST 42)

-- 3rd position of (range 1 5)
{-@ vec3 :: FieldDSL PF @-}
vec3 :: DSL PF
vec3 = get TF (range 1 5) 3 where

-- multiply two vectors component-wise
{-@ vecMul :: a:VecDSL p TF ->
              b:{VecDSL p TF | vlength b = vlength a} ->
              c:{VecDSL p TF | vlength c = vlength a} @-}
vecMul :: Num p => DSL p -> DSL p -> DSL p
vecMul = vZipWith TF TF TF times

-- [1, 2, 3] * [5, 6, 7] = [1*5, 2*6, 3*7] = [5, 12, 21]
{-@ vec4 :: VecDSL PF TF @-}
vec4 :: DSL PF
vec4 = vecMul (range 1 4) (range 5 8)

{-@ vec5 :: VecDSL PF TF @-}
vec5 :: DSL PF
vec5 = rotateL TF (range 1 10) 3

{-@ vec6 :: VecDSL PF TF @-}
vec6 :: DSL PF
vec6 = rotateR TF (range 1 10) 2

{-@ vec7 :: GlobalStore PF (FieldDSL PF) @-}
vec7 :: GlobalStore PF (DSL PF)
vec7 = fromBinary $ PlinkLib.fromList TBool $ map boolFromIntegral [1,1,0,1]

testVectors :: IO ()
testVectors = do
  test (pure vec1) (M.fromList [("a",1), ("b",2)]) -- [42,3,7]

  test (pure vec2) M.empty -- [1,2,42,4]
  test (pure vec3) M.empty -- 4
  test (pure vec4) M.empty -- [5,12,21]

  test (pure vec5) M.empty -- [4,5,6,7,8,9,1,2,3]
  test (pure vec6) M.empty -- [8,9,1,2,3,4,5,6,7]

  test vec7 M.empty -- 0b1101 = 13

-- Modular arithmetic examples -------------------------------------------------

{-@ mod1 :: GlobalStore PF (FieldDSL PF) @-}
mod1 :: GlobalStore PF (DSL PF)
mod1 = addMod 5 (VAR "x" TF) (VAR "y" TF)


{-@ shift :: GlobalStore PF (FieldDSL PF) @-}
shift :: GlobalStore PF (DSL PF)
shift = do
  let x = VAR "x" TF
  vec <- toBinary 3 x
  y   <- fromBinary (shiftR vec 1)
  return y


{-@ rotate :: GlobalStore PF (FieldDSL PF) @-}
rotate :: GlobalStore PF (DSL PF)
rotate = do
  let x = VAR "x" TF
  vec <- toBinary 5 x
  res <- binaryValue (rotateR TBool vec 2)
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

{-@ sha256_1 :: GlobalStore BigPF (VecDSL BigPF TBool) @-}
sha256_1 :: GlobalStore BigPF (DSL BigPF)
sha256_1 = sha256 "Hello, world!"

{-@ sha256_2 :: GlobalStore BigPF (VecDSL BigPF TBool) @-}
sha256_2 :: GlobalStore BigPF (DSL BigPF)
sha256_2 = sha256 ""

{-@ sha256_3 :: GlobalStore BigPF (VecDSL BigPF TBool) @-}
sha256_3 :: GlobalStore BigPF (DSL BigPF)
sha256_3 = sha256 "The quick brown fox jumps over the lazy dog"

{-@ sha256_4 :: GlobalStore BigPF (VecDSL BigPF TBool) @-}
sha256_4 :: GlobalStore BigPF (DSL BigPF)
sha256_4 = sha256 (replicate 64 'a')

{-@ sha256_5 :: GlobalStore BigPF (VecDSL BigPF TBool) @-}
sha256_5 :: GlobalStore BigPF (DSL BigPF)
sha256_5 = sha256 (replicate (2*64) 'a')

{-@ sha256_6 :: GlobalStore BigPF (VecDSL BigPF TBool) @-}
sha256_6 :: GlobalStore BigPF (DSL BigPF)
sha256_6 = sha256 (replicate (3*64) 'a')

{-@ sha256_7 :: GlobalStore BigPF (VecDSL BigPF TBool) @-}
sha256_7 :: GlobalStore BigPF (DSL BigPF)
sha256_7 = sha256 (replicate (4*64) 'a')

testSha :: IO ()
testSha = do
  test sha256_1 M.empty
  -- test sha256_2 M.empty
  -- test sha256_3 M.empty
  -- test sha256_4 M.empty
  -- test sha256_5 M.empty
  -- test sha256_6 M.empty
  -- test sha256_7 M.empty

-- Poseidon2 examples ----------------------------------------------------------

poseidon2_1 :: GlobalStore F_BLS12 (DSL F_BLS12)
poseidon2_1 = pure $ sbox_p bls12_3 (VAR "x" TF)

{-@ poseidon2_2 :: VecDSL' F_BLS12 3 @-}
poseidon2_2 :: GlobalStore F_BLS12 (DSL F_BLS12)
poseidon2_2 = pure $ permutation bls12_3 (fromList TF (map CONST [0,1,2]))

testPoseidon :: IO ()
testPoseidon = do
  test poseidon2_1 (M.fromList [("x",2)])
  test poseidon2_1 (M.fromList [("x",3)])

  test poseidon2_2 M.empty

-- Optimizations ---------------------------------------------------------------

-- (3 - (2 + 1)) + x ≡ x
{-@ opt1 :: GlobalStore BigPF (FieldDSL BigPF) @-}
opt1 :: GlobalStore BigPF (DSL BigPF)
opt1 = let p = (CONST 3 `minus` (CONST 2 `plus` CONST 1)) `plus` (VAR "x" TF)
       in inferType p ?? pure p

-- (3 - 2) * x + y ≡ x + y
{-@ opt2 :: GlobalStore BigPF (FieldDSL BigPF) @-}
opt2 :: GlobalStore BigPF (DSL BigPF)
opt2 = let p = ((CONST 3 `minus` CONST 2) `times` (VAR "x" TF)) `plus` (VAR "y" TF)
       in inferType p ?? pure p

-- (3 - 1) * x + y ≡ lincomb(2,x, 1,y)
{-@ opt3 :: GlobalStore BigPF (FieldDSL BigPF) @-}
opt3 :: GlobalStore BigPF (DSL BigPF)
opt3 = let p = ((CONST 3 `minus` CONST 1) `times` (VAR "x" TF)) `plus` (VAR "y" TF)
       in inferType p ?? pure p

testOpt :: IO ()
testOpt = do
  test opt1 (M.fromList [("x",7), ("y",2)])
  test opt2 (M.fromList [("x",7), ("y",2)])
  test opt3 (M.fromList [("x",7), ("y",2)])
