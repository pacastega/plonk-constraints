{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
module Treekz where

import Data.List (intercalate)
import DSL

data Tree a = N a [Tree a] deriving (Read, Show)
type Pos = (Float, Float)

compress :: Bool
compress = True

circle :: Pos -> Float -> String -> String
circle pos radius value = "\\draw " ++ show pos ++
                          -- " circle (" ++ show radius ++ "cm)" ++
                          " node {" ++ value ++ "};\n"

{-@ ignore genTikz @-}
genTikz :: Float -> Pos -> Pos -> Tree String -> String
genTikz radius (dx, dy) pos@(x, y) (N v ts) = circle pos radius v ++
  concatMap (uncurry $ drawChild radius (x, y) (dx', dy)) (zip positions ts)
  where
    n = length ts -- number of children
    n' = fromIntegral n
    dx' = if compress then dx / n' else dx
    xPositions = take n (iterate (+ 2*dx / n') (x - dx + dx / n'))
    positions = zip xPositions (repeat $ y-dy)


drawChild :: Float -> Pos -> Pos -> Pos -> Tree String -> String
drawChild radius pos (dx, dy) childPos child =
  line pos childPos radius ++ genTikz radius (dx, dy) childPos child

genTikzs :: Float -> Pos -> [Tree String] -> String
genTikzs r delta trees = concatMap aux trees where
  aux tree = "\\begin{tikzpicture}\n" ++
             genTikz r delta (0,0) tree ++
             "\\end{tikzpicture}\n\\newpage\n"

parse :: (Show p, Show i) => LDSL p i -> Tree String
parse p = case p of
  LWIRE i        -> N (wire [i])                []

  LVAR s i       -> N ("$" ++ s ++ "$" ++ wire [i])         []
  LCONST x i     -> N (show x ++ wire [i])      []
  LADD p1 p2 i   -> N ("$+$" ++ wire [i])       [parse p1, parse p2]
  LSUB p1 p2 i   -> N ("$-$" ++ wire [i])       [parse p1, parse p2]
  LMUL p1 p2 i   -> N ("$\times$" ++ wire [i])  [parse p1, parse p2]
  LDIV p1 p2 i   -> N ("$/$" ++ wire [i])       [parse p1, parse p2]

  LNOT p1    i   -> N ("$\\neg$" ++ wire [i])    [parse p1]
  LAND p1 p2 i   -> N ("$\\wedge$" ++ wire [i]) [parse p1, parse p2]
  LOR  p1 p2 i   -> N ("$\\vee$" ++ wire [i])   [parse p1, parse p2]
  LXOR p1 p2 i   -> N ("$\\oplus$" ++ wire [i]) [parse p1, parse p2]

  LUnsafeNOT p1    i   -> N ("$\\hat\\neg$" ++ wire [i])    [parse p1]
  LUnsafeAND p1 p2 i   -> N ("$\\hat\\wedge$" ++ wire [i]) [parse p1, parse p2]
  LUnsafeOR  p1 p2 i   -> N ("$\\hat\\vee$" ++ wire [i])   [parse p1, parse p2]
  LUnsafeXOR p1 p2 i   -> N ("$\\hat\\oplus$" ++ wire [i]) [parse p1, parse p2]

  LISZERO p1 i w -> N ("$ =0?$" ++ wire [i, w]) [parse p1]
  LEQLC p1 k i w -> N ("$ =" ++ show k ++ "?$" ++ wire [i, w]) [parse p1]
  where
    wire l = "\\textcolor{red}{\\tiny " ++ (intercalate "," (map show l)) ++ "}"

norm :: Pos -> Float
norm (x, y) = sqrt (x*x + y*y)

{-@ ignore normalize @-}
normalize :: Pos -> Pos
normalize (x, y) = (x/d, y/d) where d = norm (x, y)

{-@ ignore line @-}
line :: Pos -> Pos -> Float -> String
line (x1, y1) (x2, y2) r = "\\draw "
  ++ show pos1' ++ " -- " ++ show pos2' ++ ";\n"
  where
    (dx, dy) = normalize (x2-x1, y2-y1)
    pos1' = (x1 + r*dx, y1 + r*dy)
    pos2' = (x2 - r*dx, y2 - r*dy)

intro :: String
intro = "\\documentclass{article}\n\
         \\\usepackage{tikz}\n\
         \\\usepackage[margin=0.5cm,landscape]{geometry}\n\
         \\\begin{document}\n\
         \\\centering\n"

outro :: String
outro = "\\end{document}\n"
