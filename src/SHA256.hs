{-# OPTIONS -Wno-type-defaults #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
{-@ infix +++ @-}
module SHA256 (sha256) where

import Prelude hiding (Word)

import DSL
import PlinkLib
import Utils
import GlobalStore

import Data.Char (ord)

{-@ type Word p = {d:DSL p | typed d TF} @-}
type Word p = DSL p

{-@ h :: ListN (Word p) 8 @-}
h :: Num p => [Word p]
h = [ CONST 0x6a09e667
    , CONST 0xbb67ae85
    , CONST 0x3c6ef372
    , CONST 0xa54ff53a
    , CONST 0x510e527f
    , CONST 0x9b05688c
    , CONST 0x1f83d9ab
    , CONST 0x5be0cd19
    ]

{-@ k :: ListN (Word p) 64 @-}
k :: Num p => [Word p]
k = [ CONST 0x428a2f98
    , CONST 0x71374491
    , CONST 0xb5c0fbcf
    , CONST 0xe9b5dba5
    , CONST 0x3956c25b
    , CONST 0x59f111f1
    , CONST 0x923f82a4
    , CONST 0xab1c5ed5

    , CONST 0xd807aa98
    , CONST 0x12835b01
    , CONST 0x243185be
    , CONST 0x550c7dc3
    , CONST 0x72be5d74
    , CONST 0x80deb1fe
    , CONST 0x9bdc06a7
    , CONST 0xc19bf174

    , CONST 0xe49b69c1
    , CONST 0xefbe4786
    , CONST 0x0fc19dc6
    , CONST 0x240ca1cc
    , CONST 0x2de92c6f
    , CONST 0x4a7484aa
    , CONST 0x5cb0a9dc
    , CONST 0x76f988da

    , CONST 0x983e5152
    , CONST 0xa831c66d
    , CONST 0xb00327c8
    , CONST 0xbf597fc7
    , CONST 0xc6e00bf3
    , CONST 0xd5a79147
    , CONST 0x06ca6351
    , CONST 0x14292967

    , CONST 0x27b70a85
    , CONST 0x2e1b2138
    , CONST 0x4d2c6dfc
    , CONST 0x53380d13
    , CONST 0x650a7354
    , CONST 0x766a0abb
    , CONST 0x81c2c92e
    , CONST 0x92722c85

    , CONST 0xa2bfe8a1
    , CONST 0xa81a664b
    , CONST 0xc24b8b70
    , CONST 0xc76c51a3
    , CONST 0xd192e819
    , CONST 0xd6990624
    , CONST 0xf40e3585
    , CONST 0x106aa070

    , CONST 0x19a4c116
    , CONST 0x1e376c08
    , CONST 0x2748774c
    , CONST 0x34b0bcb5
    , CONST 0x391c0cb3
    , CONST 0x4ed8aa4a
    , CONST 0x5b9cca4f
    , CONST 0x682e6ff3

    , CONST 0x748f82ee
    , CONST 0x78a5636f
    , CONST 0x84c87814
    , CONST 0x8cc70208
    , CONST 0x90befffa
    , CONST 0xa4506ceb
    , CONST 0xbef9a3f7
    , CONST 0xc67178f2
    ]

{-@ padding :: msg:{PlinkVec p TBool | vlength msg < pow 2 64}
            -> {res:PlinkVec p TBool | (vlength res) mod 512 = 0} @-}
padding :: Num p => DSL p -> DSL p
padding msg = msg +++ (fromList TBool [BOOLEAN True])
                  +++ (vReplicate TBool k (BOOLEAN False)) +++ len
  where
    l = vlength msg
    -- 512*c is the smallest multiple of 512 above l+1+64
    c = (l+64) `div` 512 + 1
    {-@ c :: {c:Int | 512*(c-1) < l+1+64 && l+1+64 <= 512*c} @-}
    k = 512*c - (l+1+64)
    {-@ k :: {k:Btwn 0 512 | l+1+k+64 = 512*c} @-}
    len = fromInt 64 l -- convert length to binary using 64 bits

    (+++) = vAppend TBool

{-@ plus :: Word p -> Word p
         -> GlobalStore p (Word p) @-}
plus :: (Integral p, Fractional p, Ord p) =>
        DSL p -> DSL p -> GlobalStore p (DSL p)
plus = addMod 32 -- addition modulo 2^32


{-@ processMsg :: {msg:PlinkVec p TBool | (vlength msg) mod 512 = 0}
               -> GlobalStore p (PlinkVec p TBool) @-}
-- TODO: can we prove the resulting length is what it should be?
processMsg :: (Integral p, Fractional p, Ord p) =>
              DSL p -> GlobalStore p (DSL p)
processMsg msg = do
  let chunks = vChunk TBool 512 msg -- split into 512-bit chunks
  finalHashes <- foldl processChunk (pure h) chunks -- process all the chunks
  finalHashes' <- sequence' $ map (toBinary 32) finalHashes -- convert to binary
  return $ vConcat TBool finalHashes' -- concatenate all the hashes

{-@ processChunk :: GlobalStore p (ListN (Word p) 8)
                 -> {v:DSL p | typed v (TVec TBool 512) && vlength v = 512}
                 -> GlobalStore p (ListN (Word p) 8) @-}
processChunk :: (Integral p, Fractional p, Ord p) =>
                GlobalStore p [Word p] -> DSL p
             -> GlobalStore p [Word p]
processChunk currentHash chunk = do
  let words = vChunk TBool 32 chunk -- split chunk as list of 16 32-bit words
  words' <- sequence' $ map fromBinary words -- convert to list of 16 32-bit ints
  extended <- extend words' -- extend to list of 64 32-bit ints

  currentHash' <- currentHash -- unwrap it

  workingVariables <- compress (pure currentHash') extended
  finalHashes <- sequence' $ zipWith' plus currentHash' workingVariables

  return finalHashes

rotate :: DSL p -> Int -> DSL p
rotate = rotateR TBool

{-@ extend :: ListN (Word p) 16 -> GlobalStore p (ListN (Word p) 64) @-}
extend :: (Integral p, Fractional p, Ord p) =>
          [Word p] -> GlobalStore p [Word p]
extend ws = go 16 (pure ws) where

  {-@ go :: n:{Int | 16 <= n && n <= 64}
         -> GlobalStore p (ListN (Word p) n)
         -> GlobalStore p (ListN (Word p) 64)
          / [64-n] @-}
  go :: (Integral p, Fractional p, Ord p) =>
        Int -> GlobalStore p [Word p]
     -> GlobalStore p [Word p]
  go i acc
    | i == 64   = acc
    | otherwise = do
        let ws = body acc

        w15 <- toBinary 32 (ws!!(i-15))
        let s0' = (rotate w15 7) `vXor` (rotate w15 18) `vXor` (shiftR w15 3)
        s0 <- fromBinary s0'

        w2 <- toBinary 32 $ ws!!(i-2)
        let s1' = (rotate w2 17) `vXor` (rotate w2 19) `vXor` (shiftR w2 10)
        s1 <- fromBinary s1'

        tmp <- return (ws!!(i-16)) >>= plus s0 >>= plus (ws!!(i-7)) >>= plus s1
        go (i+1) (return (ws ++ [tmp]))

{-@ compress :: GlobalStore p (ListN (Word p) 8) -> ListN (Word p) 64
             -> GlobalStore p (ListN (Word p) 8) @-}
compress :: (Integral p, Fractional p, Ord p) =>
            GlobalStore p [Word p] -> [Word p]
         -> GlobalStore p [Word p]
compress = aux 64 where

  {-@ aux :: l:{Nat | l <= 64}
          -> GlobalStore p (ListN (Word p) 8)
          -> ListN (Word p) l
          -> GlobalStore p (ListN (Word p) 8) @-}
  aux :: (Integral p, Fractional p, Ord p) =>
         Int -> GlobalStore p [Word p] -> [Word p]
      -> GlobalStore p [Word p]
  aux 0 acc []     = acc
  aux l acc (p:ps) = aux (l-1) (go (64-l) acc p) ps

  {-@ go :: Btwn 0 64 -> GlobalStore p (ListN (Word p) 8) -> Word p
         -> GlobalStore p (ListN (Word p) 8) @-}
  go :: (Integral p, Fractional p, Ord p)
     => Int -> GlobalStore p [Word p] -> Word p
     -> GlobalStore p [Word p]
  go i currentHash w = do
    l <- currentHash
    let [a,b,c,d,e,f,g,h] = l

    -- convert needed numbers to binary
    e' <- toBinary 32 e
    f' <- toBinary 32 f
    g' <- toBinary 32 g

    -- operate on them
    let s1' = (rotate e' 6) `vXor` (rotate e' 11) `vXor` (rotate e' 25)
    let ch' = (e' `vAnd` f') `vXor` ((vNot e') `vAnd` g')

    -- convert back to number
    s1 <- fromBinary s1'
    ch <- fromBinary ch'

    -- first temp value
    temp1 <- pure h >>= plus s1 >>= plus ch >>= plus (k!!i) >>= plus w

    -- convert needed numbers to binary
    a' <- toBinary 32 a
    b' <- toBinary 32 b
    c' <- toBinary 32 c

    -- operate on them
    let s0' = (rotate a' 2) `vXor` (rotate a' 13) `vXor` (rotate a' 22)
    let maj' = (a' `vAnd` b') `vXor` (a' `vAnd` c') `vXor` (b' `vAnd` c')

    -- convert back to number
    s0 <- fromBinary s0'
    maj <- fromBinary maj'

    -- second temp value
    temp2 <- s0 `plus` maj

    -- final value
    newA <- temp1 `plus` temp2
    newE <- d `plus` temp1
    return $ [newA, a, b, c, newE, e, f, g]

{-@ assume ord :: Char -> Btwn 0 256 @-}

{-@ sha256 :: {s:String | len s < pow 2 61} ->
              GlobalStore p (PlinkVec p TBool) @-}
sha256 :: (Integral p, Fractional p, Ord p)
       => String -> GlobalStore p (DSL p)
sha256 = processMsg . padding . toBits where
  {-@ toBits :: s:String
             -> {v:DSL p | typed v (TVec TBool (8 * len s))
                        && vlength v = 8 * len s} @-}
  toBits :: Num p => String -> DSL p
  toBits [] = NIL TBool
  toBits (c:cs) = fromInt 8 (ord c) +++ toBits cs

  (+++) = vAppend TBool
