{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Label (label) where

import TypeAliases
import DSL

import qualified Data.Map as M

type Env p i = M.Map (DSL p) i

{-@ label :: TypedDSL p
          -> Store p
          -> (m:Nat, [LDSL p Int], [LDSL p Int])
                  <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                   \_ m -> {l:[LDSL p (Btwn 0 m)] | true}> @-}
label :: (Num p, Ord p) => DSL p -> Store p -> (Int, [LDSL p Int], [LDSL p Int])
label program store = (m, labeledPrograms, labeledStore) where
  (m', labeledStore, env') = labelStore store 0 M.empty
  (m, labeledPrograms, _) = label' program m' env'

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

-- combinator to label programs with 2 arguments that need recursive labelling
{-@ lazy label2 @-}
{-@ label2 :: m0:Nat -> ScalarDSL p -> ScalarDSL p -> Env p (Btwn 0 m0) ->
              (m:{Int | m >= m0}, LDSL p Int, LDSL p Int, Env p Int)
                         <\m     -> {v:LDSL  p (Btwn 0 m)  | true},
                          \_ m   -> {v:LDSL  p (Btwn 0 m)  | true},
                          \_ _ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
label2 :: (Num p, Ord p) => Int -> DSL p -> DSL p -> Env p Int ->
          (Int, LDSL p Int, LDSL p Int, Env p Int)
label2 nextIndex arg1 arg2 env =
  let i = nextIndex
      (i1, [arg1'], env1) = label' arg1 i  env
      (i2, [arg2'], env2) = label' arg2 i1 env1
  in (i2, arg1', arg2', env2)


add :: Ord k => (k, v) -> M.Map k v -> M.Map k v
add (k,v) = M.alter (\_ -> Just v) k


{-@ lazy label' @-}
{-@ label' :: program:TypedDSL p ->
              m0:Nat -> Env p (Btwn 0 m0) ->
              (m:{Int | m >= m0}, [LDSL p Int], Env p Int)
           <\m   -> {l:[LDSL p (Btwn 0 m)] | scalar program => len l = 1},
            \_ m -> {v:Env   p (Btwn 0 m)  | true}> @-}
label' :: (Num p, Ord p) => DSL p -> Int -> Env p Int
       -> (Int, [LDSL p Int], Env p Int)
label' p nextIndex env = case M.lookup p env of
  Just i  -> (nextIndex, [LWIRE i], env)
  Nothing -> let i = nextIndex in case p of

    VAR s _ -> (i+1, [LVAR s i], add (p,i) env)
    CONST x -> (i+1, [LCONST x i], add (p,i) env)
    TRUE  -> label' (CONST 1) nextIndex env
    FALSE -> label' (CONST 0) nextIndex env

    ADD p1 p2 -> (i'+1, [LADD p1' p2' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env
    SUB p1 p2 -> (i'+1, [LSUB p1' p2' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env
    MUL p1 p2 -> (i'+1, [LMUL p1' p2' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env
    DIV p1 p2 -> (w'+1, [LDIV p1' p2' w' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env; w' = i'+1

    NOT p1    -> (i'+1, [LNOT p1' i'], add (p,i') env')
      where (i', [p1'], env') = label' p1 i env
    AND p1 p2 -> (i'+1, [LAND p1' p2' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env
    OR  p1 p2 -> (i'+1, [LOR  p1' p2' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env
    XOR p1 p2 -> (i'+1, [LXOR p1' p2' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env

    UnsafeNOT p1    -> (i'+1, [LUnsafeNOT p1' i'], add (p,i') env')
      where (i', [p1'], env') = label' p1 i env
    UnsafeAND p1 p2 -> (i'+1, [LUnsafeAND p1' p2' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env
    UnsafeOR  p1 p2 -> (i'+1, [LUnsafeOR  p1' p2' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env
    UnsafeXOR p1 p2 -> (i'+1, [LUnsafeXOR p1' p2' i'], add (p,i') env')
      where (i', p1', p2', env') = label2 i p1 p2 env

    ISZERO p1 -> (w'+1, [LISZERO p1' w' i'], add (p,i') env')
      where (i', [p1'], env') = label' p1 i env; w' = i'+1
    EQL p1 p2 -> label' (ISZERO (p1 `SUB` p2)) nextIndex env
    EQLC p1 k -> (w'+1, [LEQLC p1' k w' i'], add (p,i') env')
      where (i', [p1'], env') = label' p1 i env; w' = i'+1

    NIL _ -> (i, [], env)
    CONS h ts -> (i'', h' ++ ts', env'')
      where (i',  h',  env')  = label' h  i  env
            (i'', ts', env'') = label' ts i' env'

{-@ lazy labelStore' @-}
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
    EQA p1 p2 -> (i', [LEQA p1' p2'], env')
      where (i', p1', p2', env') = label2 i p1 p2 env
