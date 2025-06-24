{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Label where

import TypeAliases
import DSL
import Utils
import PlinkLib

import qualified Liquid.Data.Map as M

type Env p i = M.Map (DSL p) i


{-@ measure size @-}
{-@ size :: DSL p -> Nat @-}
size :: DSL p -> Int
size (VAR _ _) = 1
size (CONST _) = 1
size (BOOLEAN _) = 2 -- BOOLEAN -> CONST

size (ADD p1 p2) = 1 + size p1 + size p2
size (SUB p1 p2) = 1 + size p1 + size p2
size (MUL p1 p2) = 1 + size p1 + size p2
size (DIV p1 p2) = 1 + size p1 + size p2

size (ADDC p1 _) = 1 + size p1
size (MULC p1 _) = 1 + size p1
size (LINCOMB _ p1 _ p2) = 1 + size p1 + size p2

size (NOT p1) = 1 + size p1
size (AND p1 p2) = 1 + size p1 + size p2
size (OR  p1 p2) = 1 + size p1 + size p2
size (XOR p1 p2) = 1 + size p1 + size p2

size (UnsafeNOT p1) = 1 + size p1
size (UnsafeAND p1 p2) = 1 + size p1 + size p2
size (UnsafeOR  p1 p2) = 1 + size p1 + size p2
size (UnsafeXOR p1 p2) = 1 + size p1 + size p2

-- syntactic sugar needs extra steps to desugar
size (ISZERO p1) = 1 + size p1           + 1 --        ISZERO -> EQLC
size (EQL p1 p2) = 1 + size p1 + size p2 + 3 -- EQL -> ISZERO -> EQLC
size (EQLC p1 _) = 1 + size p1

size (NIL _) = 0
size (CONS h ts) = 1 + size h + size ts

size (BoolToF p) = 1 + size p



-- {-@ reflect label @-}
-- {-@ label :: TypedDSL p
--           -> Store p
--           -> (m:Nat, [LDSL p Int], [LDSL p Int])
--                   <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
--                    \_ m -> {l:[LDSL p (Btwn 0 m)] | true}> @-}
-- label :: (Num p, Ord p) => DSL p -> Store p -> (Int, [LDSL p Int], [LDSL p Int])
-- label program store = (m, labeledPrograms, labeledStore) where
--   (m', labeledStore, env') = labelStore store 0 M.empty
--   (m, labeledPrograms, _) = label' program m' env'

{-@ reflect labelStore @-}
{-@ labelStore :: Store p -> m0:Nat -> Env p (Btwn 0 m0)
               -> (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
                      <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                       \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
labelStore :: (Num p, Ord p) =>
              Store p -> Int -> Env p Int -> (Int, [LDSL p Int], Env p Int)
labelStore [] nextIndex env = (nextIndex, [], env)
labelStore (def:ss) nextIndex env =
  let i = nextIndex
      (i', def', env') = labelStore' def i env
      (i'', ss', env'') = labelStore ss i' env'
  in (i'', def' ++ ss', env'')


{-@ reflect add @-}
add :: Ord k => (k, v) -> M.Map k v -> M.Map k v
add (k,v) = M.alter (\_ -> Just v) k


{-@ reflect label' @-}
{-@ label' :: program:TypedDSL p ->
              m0:Nat -> Env p (Btwn 0 m0) ->
              (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
           <\m   -> {l:[LDSL p (Btwn 0 m)] | scalar program => len l = 1},
            \_ m -> {v:Env   p (Btwn 0 m)  | true}>
           / [size program] @-}
label' :: (Num p, Ord p) => DSL p -> Int -> Env p Int
       -> (Int, [LDSL p Int], Env p Int)
label' p nextIndex env = case M.lookup p env of
  Just i  -> (nextIndex, [LWIRE i], env)
  Nothing -> let i = nextIndex in case p of

    v@(VAR s τ) -> case τ of
      TF         -> (i+1, [LVAR s τ i], add (p,i) env)
      TBool      -> (i+1, [LVAR s τ i], add (p,i) env)
      TVec {}    -> label' (expandVecVar v) nextIndex env
    CONST x -> (i+1, [LCONST x i], add (p,i) env)
    BOOLEAN False  -> label' (CONST zero) nextIndex env
    BOOLEAN True   -> label' (CONST one) nextIndex env

    ADD p1 p2 -> (i'+1, [LADD p1' p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
    SUB p1 p2 -> (i'+1, [LSUB p1' p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
    MUL p1 p2 -> (i'+1, [LMUL p1' p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
    DIV p1 p2 -> (w'+1, [LDIV p1' p2' w' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
            w' = i'+1
    ADDC p1 k -> (i'+1, [LADDC p1' k i'], add (p,i') env')
      where (i', [p1'], env') = label' p1 i env
    MULC p1 k -> (i'+1, [LMULC p1' k i'], add (p,i') env')
      where (i', [p1'], env') = label' p1 i env
    LINCOMB k1 p1 k2 p2 -> (i'+1, [LLINCOMB k1 p1' k2 p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''

    NOT p1    -> (i'+1, [LNOT p1' i'], add (p,i') env')
      where (i', [p1'], env') = label' p1 i env
    AND p1 p2 -> (i'+1, [LAND p1' p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
    OR  p1 p2 -> (i'+1, [LOR  p1' p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
    XOR p1 p2 -> (i'+1, [LXOR p1' p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''

    UnsafeNOT p1    -> (i'+1, [LUnsafeNOT p1' i'], add (p,i') env')
      where (i', [p1'], env') = label' p1 i env
    UnsafeAND p1 p2 -> (i'+1, [LUnsafeAND p1' p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
    UnsafeOR  p1 p2 -> (i'+1, [LUnsafeOR  p1' p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
    UnsafeXOR p1 p2 -> (i'+1, [LUnsafeXOR p1' p2' i'], add (p,i') env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''

    ISZERO p1 -> label' (EQLC p1 zero) nextIndex env
    EQL p1 p2 -> label' (ISZERO (p1 `SUB` p2)) nextIndex env
    EQLC p1 k -> (w'+1, [LEQLC p1' k w' i'], add (p,i') env')
      where (i', [p1'], env') = label' p1 i env; w' = i'+1

    NIL _ -> (i, [], env)
    CONS h ts -> (i'', h' ++ ts', env'')
      where (i',  h',  env')  = label' h  i  env
            (i'', ts', env'') = label' ts i' env'

    BoolToF p -> label' p i env -- noop

{-@ reflect labelStore' @-}
{-@ labelStore' :: assertion:(Assertion p) ->
                   m0:Nat -> Env p (Btwn 0 m0) ->
                   (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
             <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
              \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
labelStore' :: (Num p, Ord p) => Assertion p -> Int -> Env p Int
            -> (Int, [LDSL p Int], Env p Int)
labelStore' assertion nextIndex env = let i = nextIndex in case assertion of
    DEF s d τ -> (i', [d'], add (VAR s τ, outputWire d') env')
      where (i', [d'], env') = label' d i env
    NZERO p1  -> (w'+1, [LNZERO p1' w'], env')
      where (w', [p1'], env') = label' p1 i env
    BOOL p1  -> (i', [LBOOL p1'], env')
      where (i', [p1'], env') = label' p1 i env
    EQA p1 p2 -> case M.lookup p1 env of
      Just i1 -> case M.lookup p2 env of
        Just i2 -> (i, [LEQA (LWIRE i1) (LWIRE i2)], env) -- both present
        Nothing -> (i', [withOutputWire i' i1 p2'], env'') -- use i1 for p2
          where (i', [p2'], env') = label' p2 i env
                env'' = add (p2, i1) env'
      Nothing -> case M.lookup p2 env of
        Just i2 -> (i', [withOutputWire i' i2 p1'], env'')
          where (i', [p1'], env') = label' p1 i env       -- use i2 for p1
                env'' = add (p1, i2) env'
        Nothing -> (i'', [p1', withOutputWire i'' i1 p2'], env''')
          where (i' , [p1'], env')  = label' p1 i  env
                (i'', [p2'], env'') = label' p2 i' env'
                i1 = outputWire p1'
                env''' = add (p2, i1) env'' -- arbitrarily choose i1 for both


{-@ reflect withOutputWire @-}
{-@ withOutputWire :: m:Nat -> Btwn 0 m -> LDSL p (Btwn 0 m)
                   -> LDSL p (Btwn 0 m) @-}
withOutputWire :: Int -> Int -> LDSL p Int -> LDSL p Int
withOutputWire _ i program = case program of
  LWIRE _ -> LWIRE i
  LVAR s τ _ -> LVAR s τ i
  LCONST p _ -> LCONST p i

  LADD p1 p2 _ -> LADD p1 p2 i
  LSUB p1 p2 _ -> LSUB p1 p2 i
  LMUL p1 p2 _ -> LMUL p1 p2 i
  LDIV p1 p2 w _ -> LDIV p1 p2 w i

  LADDC p k _ -> LADDC p k i
  LMULC p k _ -> LMULC p k i
  LLINCOMB k1 p1 k2 p2 _ -> LLINCOMB k1 p1 k2 p2 i

  LNOT p1 _ -> LNOT p1 i
  LAND p1 p2 _ -> LAND p1 p2 i
  LOR  p1 p2 _ -> LOR  p1 p2 i
  LXOR p1 p2 _ -> LXOR p1 p2 i

  LUnsafeNOT p1 _ -> LUnsafeNOT p1 i
  LUnsafeAND p1 p2 _ -> LUnsafeAND p1 p2 i
  LUnsafeOR  p1 p2 _ -> LUnsafeOR  p1 p2 i
  LUnsafeXOR p1 p2 _ -> LUnsafeXOR p1 p2 i

  LEQLC   p1 k w _ -> LEQLC p1 k w i

  LNZERO p1 _ -> LNZERO p1 i
  LBOOL  p1 -> LBOOL p1
  LEQA p1 p2 -> LEQA p1 p2
