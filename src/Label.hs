{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-with-undecided-guards" @-}
module Label where

import TypeAliases
import DSL
import Utils

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

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
          -> (m:Nat, LDSL p Int, [LAss p Int])
                  <\m   -> {l:LDSL p (Btwn 0 m) | true},
                   \_ m -> {l:[LAss p (Btwn 0 m)] | true}> @-}
label :: (Num p, Ord p) => DSL p -> Store p -> (Int, LDSL p Int, [LAss p Int])
label program store = (m, labeledPrograms, labeledStore) where
  (m', labeledStore, λ') = labelAs store 0 M.empty
  (m, labeledPrograms, _λ) = labelE program m' λ'

#else

-- version WITH CSE

type ExtLabelEnv p i = M.Map (DSL p) i

label :: (Num p, Ord p) => DSL p -> Store p -> (Int, LDSL p Int, [LAss p Int])
label program store = (m, labeledProgram, labeledStore) where
  (m', labeledStore, λ') = labelAs_CSE store 0 M.empty
  (m, labeledProgram, _λ) = labelE_CSE program m' λ'

labelAs_CSE :: (Num p, Ord p)
            => Store p -> Int -> ExtLabelEnv p Int
            -> (Int, [LAss p Int], ExtLabelEnv p Int)
labelAs_CSE [] nextIndex λ = (nextIndex, [], λ)
labelAs_CSE (def:ss) nextIndex λ =
  let i = nextIndex
      (i', def', λ') = labelA_CSE def i λ
      (i'', s'', λ'') = labelAs_CSE ss i' λ'
  in (i'', def' : s'', λ'')

labelA_CSE :: (Num p, Ord p) => Assertion p -> Int -> ExtLabelEnv p Int
           -> (Int, LAss p Int, ExtLabelEnv p Int)
labelA_CSE assertion nextIndex λ = let i = nextIndex in case assertion of
    NZERO p1  -> (w'+1, LNZERO p1' w', λ')
      where (w', p1', λ') = labelE_CSE p1 i λ
    BOOLEAN p1  -> (i', LBOOLEAN p1', λ')
      where (i', p1', λ') = labelE_CSE p1 i λ
    EQA p1 p2 -> case M.lookup p1 λ of
      Just i1 -> case M.lookup p2 λ of
        Just i2 -> (i, LEQA (PTR τ1 i1) (PTR τ2 i2), λ) -- both are labeled: can't relabel them
          where Just τ1 = inferType p1; Just τ2 = inferType p2
        Nothing -> (i', LEQA (PTR τ1 i1) p2', λ')
          where (i', p2', λ') = labelE_CSE p2 i λ
                Just τ1 = inferType p1
      Nothing -> case M.lookup p2 λ of
        Just i2 -> (i', LEQA p1' (PTR τ2 i2), λ')
          where (i', p1', λ') = labelE_CSE p1 i λ
                Just τ2 = inferType p2
        Nothing -> (i'', LEQA p1' p2', λ'')
          where (i' , p1', λ')  = labelE_CSE p1 i  λ
                (i'', p2', λ'') = labelE_CSE p2 i' λ'


labelE_CSE :: (Num p, Ord p) => DSL p -> Int -> ExtLabelEnv p Int
           -> (Int, LDSL p Int, ExtLabelEnv p Int)
labelE_CSE p nextIndex λ = case M.lookup p λ of
  Just i  -> let Just τ = inferType p in (nextIndex, PTR τ i, λ)
  Nothing -> let i = nextIndex in case p of

    VAR s τ -> (i+1, LVAR s τ i, M.insert p i λ)
    CONST x -> (i+1, LCONST x i, M.insert p i λ)
    BOOL False -> labelE_CSE (CONST zero) nextIndex λ
    BOOL True  -> labelE_CSE (CONST one) nextIndex λ

    UN op p1 -> case op of
      BoolToF -> labelE_CSE p1 i λ -- noop
      ISZERO -> labelE_CSE (UN (EQLC zero) p1) nextIndex λ
      EQLC k -> (w'+1, LEQLC p1' k w' i', M.insert p i' λ')
        where (i', p1', λ') = labelE_CSE p1 i λ; w' = i'+1
      _ -> (i'+1, LUN op p1' i', M.insert p i' λ')
        where (i', p1', λ') = labelE_CSE p1 i λ

    BIN op p1 p2 -> case op of
      DIV -> (w'+1, LDIV p1' p2' w' i', M.insert p i' λ')
        where (i'', p1', λ'') = labelE_CSE p1 i   λ
              (i' , p2', λ')  = labelE_CSE p2 i'' λ''
              w' = i'+1
      EQL -> labelE_CSE (UN (EQLC zero) (BIN SUB p1 p2)) nextIndex λ
      _ -> (i'+1, LBIN op p1' p2' i', M.insert p i' λ')
        where (i'', p1', λ'') = labelE_CSE p1 i   λ
              (i' , p2', λ')  = labelE_CSE p2 i'' λ''

    NIL τ -> (i, LNIL τ, λ)
    CONS h ts -> (i'', LCONS h' ts', λ'')
      where (i',  h',  λ')  = labelE_CSE h  i  λ
            (i'', ts', λ'') = labelE_CSE ts i' λ'

#endif

-- even if we're not using LH, we still need the below functions because
-- they appear in proofs
--------------------------------------------------------------------------------

{-@ reflect labelE @-}
{-@ labelE :: e:TypedDSL p
           -> m0:Nat -> LabelEnv p (Btwn 0 m0)
           -> (m:{Int | m >= m0}, LDSL p Int, LabelEnv p Int)
           <\m   -> {e':LDSLI p (Btwn m0 m) (Btwn 0 m) | inferType' e' = inferType e},
            \_ m -> {v:LabelEnv p (Btwn 0 m) | true}>
           / [size e] @-}
labelE :: (Num p, Ord p) => DSL p -> Int -> LabelEnv p Int
       -> (Int, LDSL p Int, LabelEnv p Int)
labelE p i λ = case p of
    VAR s τ -> case M.lookup s λ of
      Nothing -> (i+1, LVAR s τ i, M.insert s i λ)
      Just j -> (i, PTR τ j, λ)

    CONST x -> (i+1, LCONST x i, λ)
    BOOL b -> (i+1, LBOOL b i, λ)

    UN op p1 -> case op of
      BoolToF -> (i1, LBoolToF p1', λ1)
        where (i1, p1', λ1) = labelE p1 i λ
      ISZERO -> labelE (UN (EQLC zero) p1) i λ
      EQLC k -> (w+1, LEQLC p1' k w i1, λ1)
        where (i1, p1', λ1) = labelE p1 i λ; w = i1+1
      _ -> (i1+1, LUN op p1' i1, λ1)
        where (i1, p1', λ1) = labelE p1 i λ

    BIN op p1 p2 -> case op of
      DIV -> (w+1, LDIV p1' p2' w i2, λ2)
        where (i1, p1', λ1) = labelE p1 i  λ
              (i2, p2', λ2) = labelE p2 i1 λ1
              w = i2+1
      EQL -> labelE (UN (EQLC zero) (BIN SUB p1 p2)) i λ
      _ -> (i2+1, LBIN op p1' p2' i2, λ2)
        where (i1, p1', λ1) = labelE p1 i  λ
              (i2, p2', λ2) = labelE p2 i1 λ1

    NIL τ -> (i, LNIL τ, λ)
    CONS h ts -> (i2, LCONS h' ts', λ2)
      where (i1,  h', λ1) = labelE h  i  λ
            (i2, ts', λ2) = labelE ts i1 λ1

{-@ reflect labelA @-}
{-@ labelA :: assertion:(Assertion p)
           -> m0:Nat -> LabelEnv p (Btwn 0 m0)
           -> (m:{Int | m >= m0}, LAss p Int, LabelEnv p Int)
                <\m   -> {l:LAssI p (Btwn m0 m) (Btwn 0 m) | true},
                 \_ m -> {v:LabelEnv p (Btwn 0 m) | true}> @-}
labelA :: (Num p, Ord p) => Assertion p -> Int -> LabelEnv p Int
       -> (Int, LAss p Int, LabelEnv p Int)
labelA assertion nextIndex λ = let i = nextIndex in case assertion of
    NZERO p1  -> (w'+1, LNZERO p1' w', λ')
      where (w', p1', λ') = labelE p1 i λ
    BOOLEAN p1  -> (i', LBOOLEAN p1', λ')
      where (i', p1', λ') = labelE p1 i λ
    EQA p1 p2 -> (i', LEQA p1' p2', λ')
      where (i'', p1', λ'') = labelE p1 i   λ
            (i' , p2', λ')  = labelE p2 i'' λ''

{-@ reflect labelAs @-}
{-@ labelAs :: Store p -> m0:Nat -> LabelEnv p (Btwn 0 m0)
            -> (m:{Int | m >= m0}, [LAss p Int], LabelEnv p Int)
                   <\m   -> {l:[LAssI p (Btwn m0 m) (Btwn 0 m)] | true},
                    \_ m -> {v:LabelEnv   p (Btwn 0 m)  | true}> @-}
labelAs :: (Num p, Ord p)
        => Store p -> Int -> LabelEnv p Int -> (Int, [LAss p Int], LabelEnv p Int)
labelAs [] nextIndex λ = (nextIndex, [], λ)
labelAs (def:ss) nextIndex λ =
  let i = nextIndex
      (i', def', λ') = labelA def i λ
      (i'', ss', λ'') = labelAs ss i' λ'
  in (i'', def' : ss', λ'')
