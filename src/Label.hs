{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Label where

import TypeAliases
import DSL
import Utils
import PlinkLib

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
#endif

type LabelEnv i = M.Map (Var,Ty) i


{-@ measure size @-}
{-@ size :: DSL p -> Nat @-}
size :: DSL p -> Int
size (VAR _ _) = 1
size (CONST _) = 1
size (BOOLEAN _) = 2 -- syntactic sugar: BOOLEAN -> CONST

size (UN op p1) = case op of
  ISZERO -> 1 + size p1 + 1 -- syntactic sugar: ISZERO -> EQLC
  _      -> 1 + size p1

size (BIN op p1 p2) = case op of
  EQL -> 1 + size p1 + size p2 + 3 -- syntactic sugar: EQL -> ISZERO -> EQLC
  _   -> 1 + size p1 + size p2

size (NIL _) = 0
size (CONS h ts) = 1 + size h + size ts


{-@ reflect label @-}
{-@ label :: TypedDSL p
          -> Store p
          -> (m:Nat, [LDSL p Int], [LDSL p Int])
                  <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                   \_ m -> {l:[LDSL p (Btwn 0 m)] | true}> @-}
label :: (Num p, Ord p) => DSL p -> Store p -> (Int, [LDSL p Int], [LDSL p Int])
label program store = (m, labeledPrograms, labeledStore) where
  (m', labeledStore, env') = labelStore store 0 M.empty
  (m, labeledPrograms, _) = label' program m' env'

{-@ reflect labelStore @-}
{-@ labelStore :: Store p -> m0:Nat -> LabelEnv (Btwn 0 m0)
               -> (m:{Int | m >= m0}, [LDSL p Int], LabelEnv Int)
                      <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                       \_ m -> {v:LabelEnv (Btwn 0 m) | true}> @-}
labelStore :: (Num p, Ord p) =>
              Store p -> Int -> LabelEnv Int -> (Int, [LDSL p Int], LabelEnv Int)
labelStore [] nextIndex env = (nextIndex, [], env)
labelStore (def:ss) nextIndex env =
  let i = nextIndex
      (i', def', env') = labelStore' def i env
      (i'', ss', env'') = labelStore ss i' env'
  in (i'', def' ++ ss', env'')


{-@ reflect label' @-}
{-@ label' :: program:TypedDSL p ->
              m0:Nat -> LabelEnv (Btwn 0 m0) ->
              (m:{Int | m >= m0}, [LDSL p Int], LabelEnv Int)
           <\m   -> {l:[LDSL p (Btwn 0 m)] | scalar program => len l = 1},
            \_ m -> {v:LabelEnv (Btwn 0 m) | true}>
           / [size program] @-}
label' :: (Num p, Ord p) => DSL p -> Int -> LabelEnv Int
       -> (Int, [LDSL p Int], LabelEnv Int)
label' p nextIndex env = let i = nextIndex in case p of
    VAR s τ -> case M.lookup (s,τ) env of
      Nothing -> (i+1, [LVAR s τ i], M.insert (s,τ) i env)
      Just j -> (nextIndex, [LWIRE τ j], env)

    CONST x -> (i+1, [LCONST x i], env)
    BOOLEAN False  -> label' (CONST zero) nextIndex env
    BOOLEAN True   -> label' (CONST one) nextIndex env

    UN op p1 -> case op of
      BoolToF -> label' p1 i env -- noop
      ISZERO -> label' (UN (EQLC zero) p1) nextIndex env
      EQLC k -> (w'+1, [LEQLC p1' k w' i'], env')
        where (i', [p1'], env') = label' p1 i env; w' = i'+1
      _ -> (i'+1, [LUN op p1' i'], env')
        where (i', [p1'], env') = label' p1 i env

    BIN op p1 p2 -> case op of
      DIV -> (w'+1, [LDIV p1' p2' w' i'], env')
        where (i'', [p1'], env'') = label' p1 i   env
              (i' , [p2'], env')  = label' p2 i'' env''
              w' = i'+1
      EQL -> label' (UN ISZERO (BIN SUB p1 p2)) nextIndex env
      _ -> (i'+1, [LBIN op p1' p2' i'], env')
        where (i'', [p1'], env'') = label' p1 i   env
              (i' , [p2'], env')  = label' p2 i'' env''

    NIL _ -> (i, [], env)
    CONS h ts -> (i'', h' ++ ts', env'')
      where (i',  h',  env')  = label' h  i  env
            (i'', ts', env'') = label' ts i' env'


{-@ reflect labelStore' @-}
{-@ labelStore' :: assertion:(Assertion p) ->
                   m0:Nat -> LabelEnv (Btwn 0 m0) ->
                   (m:{Int | m >= m0}, [LDSL p Int], LabelEnv Int)
             <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
              \_ m -> {v:LabelEnv (Btwn 0 m) | true}> @-}
labelStore' :: (Num p, Ord p) => Assertion p -> Int -> LabelEnv Int
            -> (Int, [LDSL p Int], LabelEnv Int)
labelStore' assertion nextIndex env = let i = nextIndex in case assertion of
    DEF s d τ -> (i', [d'], M.insert (s,τ) (outputWire d') env')
      where (i', [d'], env') = label' d i env
    NZERO p1  -> (w'+1, [LNZERO p1' w'], env')
      where (w', [p1'], env') = label' p1 i env
    BOOL p1  -> (i', [LBOOL p1'], env')
      where (i', [p1'], env') = label' p1 i env
    EQA p1 p2 -> (i', [LEQA p1' p2'], env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
