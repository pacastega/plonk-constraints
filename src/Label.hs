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

type LabelEnv p i = M.Map String i


{-@ measure size @-}
{-@ size :: DSL p -> Nat @-}
size :: DSL p -> Int
size (VAR _ _) = 1
size (CONST _) = 1
size (BOOL _) = 2 -- syntactic sugar: BOOL -> CONST

size (UN op p1) = case op of
  ISZERO -> 1 + size p1 + 1 -- syntactic sugar: ISZERO -> EQLC
  _      -> 1 + size p1

size (BIN op p1 p2) = case op of
  EQL -> 1 + size p1 + size p2 + 3 -- syntactic sugar: EQL -> ISZERO -> EQLC
  _   -> 1 + size p1 + size p2

size (NIL _) = 0
size (CONS h ts) = 1 + size h + size ts


-- disable CSE only when LH is on (for the proof of correctness) ---------------

#if LiquidOn

-- version WITHOUT CSE
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

#else

-- version WITH CSE

type ExtLabelEnv p i = M.Map (DSL p) i

label :: (Num p, Ord p) => DSL p -> Store p -> (Int, [LDSL p Int], [LDSL p Int])
label program store = (m, labeledPrograms, labeledStore) where
  (m', labeledStore, env') = labelStoreCSE store 0 M.empty
  (m, labeledPrograms, _) = labelCSE' program m' env'

labelStoreCSE :: (Num p, Ord p)
              => Store p -> Int -> ExtLabelEnv p Int
              -> (Int, [LDSL p Int], ExtLabelEnv p Int)
labelStoreCSE [] nextIndex env = (nextIndex, [], env)
labelStoreCSE (def:ss) nextIndex env =
  let i = nextIndex
      (i', def', env') = labelStoreCSE' def i env
      (i'', s'', env'') = labelStoreCSE ss i' env'
  in (i'', def' ++ s'', env'')

labelStoreCSE' :: (Num p, Ord p) => Assertion p -> Int -> ExtLabelEnv p Int
            -> (Int, [LDSL p Int], ExtLabelEnv p Int)
labelStoreCSE' assertion nextIndex env = let i = nextIndex in case assertion of
    NZERO p1  -> (w'+1, [LNZERO p1' w'], env')
      where (w', [p1'], env') = labelCSE' p1 i env
    BOOLEAN p1  -> (i', [LBOOLEAN p1'], env')
      where (i', [p1'], env') = labelCSE' p1 i env
    EQA p1 p2 -> case M.lookup p1 env of
      Just i1 -> case M.lookup p2 env of
        Just i2 -> (i, [LEQA (LWIRE τ1 i1) (LWIRE τ2 i2)], env) -- both are labeled: can't relabel them
          where Just τ1 = inferType p1; Just τ2 = inferType p2
        Nothing -> (i', [withOutputWire i' i1 p2'], env'') -- use i1 for p2
          where (i', [p2'], env') = labelCSE' p2 i env
                env'' = M.insert p2 i1 env'
      Nothing -> case M.lookup p2 env of
        Just i2 -> (i', [withOutputWire i' i2 p1'], env'') -- use i2 for p1
          where (i', [p1'], env') = labelCSE' p1 i env
                env'' = M.insert p1 i2 env'
        Nothing -> (i'', [p1', withOutputWire i'' i1 p2'], env''')
          where (i' , [p1'], env')  = labelCSE' p1 i  env
                (i'', [p2'], env'') = labelCSE' p2 i' env'
                i1 = outputWire p1'
                env''' = M.insert p2 i1 env'' -- arbitrarily choose i1 for both


{-@ withOutputWire :: m:Nat -> Btwn 0 m -> LDSL p (Btwn 0 m)
                   -> LDSL p (Btwn 0 m) @-}
withOutputWire :: Int -> Int -> LDSL p Int -> LDSL p Int
withOutputWire _ i program = case program of
  LWIRE  τ _ -> LWIRE τ i
  LVAR s τ _ -> LVAR s τ i
  LCONST p _ -> LCONST p i

  LDIV p1 p2 w _ -> LDIV p1 p2 w i

  LUN  op p1    _ -> LUN  op p1    i
  LBIN op p1 p2 _ -> LBIN op p1 p2 i

  LEQLC   p1 k w _ -> LEQLC p1 k w i

  LNZERO p1 w  -> LNZERO p1 w
  LBOOLEAN  p1 -> LBOOLEAN p1
  LEQA   p1 p2 -> LEQA p1 p2


labelCSE' :: (Num p, Ord p) => DSL p -> Int -> ExtLabelEnv p Int
          -> (Int, [LDSL p Int], ExtLabelEnv p Int)
labelCSE' p nextIndex env = case M.lookup p env of
  Just i  -> let Just τ = inferType p in (nextIndex, [LWIRE τ i], env)
  Nothing -> let i = nextIndex in case p of

    VAR s τ -> (i+1, [LVAR s τ i], M.insert p i env)
    CONST x -> (i+1, [LCONST x i], M.insert p i env)
    BOOL False -> labelCSE' (CONST zero) nextIndex env
    BOOL True  -> labelCSE' (CONST one) nextIndex env

    UN op p1 -> case op of
      BoolToF -> labelCSE' p1 i env -- noop
      ISZERO -> labelCSE' (UN (EQLC zero) p1) nextIndex env
      EQLC k -> (w'+1, [LEQLC p1' k w' i'], M.insert p i' env')
        where (i', [p1'], env') = labelCSE' p1 i env; w' = i'+1
      _ -> (i'+1, [LUN op p1' i'], M.insert p i' env')
        where (i', [p1'], env') = labelCSE' p1 i env

    BIN op p1 p2 -> case op of
      DIV -> (w'+1, [LDIV p1' p2' w' i'], M.insert p i' env')
        where (i'', [p1'], env'') = labelCSE' p1 i   env
              (i' , [p2'], env')  = labelCSE' p2 i'' env''
              w' = i'+1
      EQL -> labelCSE' (UN ISZERO (BIN SUB p1 p2)) nextIndex env
      _ -> (i'+1, [LBIN op p1' p2' i'], M.insert p i' env')
        where (i'', [p1'], env'') = labelCSE' p1 i   env
              (i' , [p2'], env')  = labelCSE' p2 i'' env''

    NIL _ -> (i, [], env)
    CONS h ts -> (i'', h' ++ ts', env'')
      where (i',  h',  env')  = labelCSE' h  i  env
            (i'', ts', env'') = labelCSE' ts i' env'

#endif

-- even if we're not using LH, we still need the below functions because
-- they appear in proofs
--------------------------------------------------------------------------------

{-@ reflect labelStore @-}
{-@ labelStore :: Store p -> m0:Nat -> LabelEnv p (Btwn 0 m0)
               -> (m:{Int | m >= m0}, [LDSL p Int], LabelEnv p Int)
                      <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
                       \_ m -> {v:LabelEnv   p (Btwn 0 m)  | true}> @-}
labelStore :: (Num p, Ord p) =>
              Store p -> Int -> LabelEnv p Int -> (Int, [LDSL p Int], LabelEnv p Int)
labelStore [] nextIndex env = (nextIndex, [], env)
labelStore (def:ss) nextIndex env =
  let i = nextIndex
      (i', def', env') = labelAssertion def i env
      (i'', ss', env'') = labelStore ss i' env'
  in (i'', def' ++ ss', env'')


{-@ reflect label' @-}
{-@ label' :: program:TypedDSL p ->
              m0:Nat -> LabelEnv p (Btwn 0 m0) ->
              (m:{Int | m >= m0}, [LDSL p Int], LabelEnv p Int)
           <\m   -> {l:[LDSL p (Btwn 0 m)] | scalar program => len l = 1},
            \_ m -> {v:LabelEnv   p (Btwn 0 m)  | true}>
           / [size program] @-}
label' :: (Num p, Ord p) => DSL p -> Int -> LabelEnv p Int
       -> (Int, [LDSL p Int], LabelEnv p Int)
label' p nextIndex env = let i = nextIndex in case p of
    VAR s τ -> case M.lookup s env of
      Nothing -> (i+1, [LVAR s τ i], M.insert s i env)
      Just j -> (nextIndex, [LWIRE τ j], env)

    CONST x -> (i+1, [LCONST x i], env)
    BOOL False -> label' (CONST zero) nextIndex env
    BOOL True  -> label' (CONST one) nextIndex env

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


{-@ reflect labelAssertion @-}
{-@ labelAssertion :: assertion:(Assertion p) ->
                   m0:Nat -> LabelEnv p (Btwn 0 m0) ->
                   (m:{Int | m >= m0}, [LDSL p Int], LabelEnv p Int)
             <\m   -> {l:[LDSL p (Btwn 0 m)] | true},
              \_ m -> {v:LabelEnv   p (Btwn 0 m)  | true}> @-}
labelAssertion :: (Num p, Ord p) => Assertion p -> Int -> LabelEnv p Int
            -> (Int, [LDSL p Int], LabelEnv p Int)
labelAssertion assertion nextIndex env = let i = nextIndex in case assertion of
    NZERO p1  -> (w'+1, [LNZERO p1' w'], env')
      where (w', [p1'], env') = label' p1 i env
    BOOLEAN p1  -> (i', [LBOOLEAN p1'], env')
      where (i', [p1'], env') = label' p1 i env
    EQA p1 p2 -> (i', [LEQA p1' p2'], env')
      where (i'', [p1'], env'') = label' p1 i   env
            (i' , [p2'], env')  = label' p2 i'' env''
