{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--ple-with-undecided-guards" @-}
module WitnessGenProof.UniquenessLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import TypeAliases
import Utils
import DSL
import Label
import MapLemmas
import Language.Haskell.Liquid.ProofCombinators

{-@ labelWFPtr :: e:TypedDSL p -> m0:Nat
               -> m:{Nat | m >= m0} -> e':LDSL p (Btwn 0 m)
               -> λ':{LabelEnv p (Btwn 0 m) | labelE e m0 M.empty = (m,e',λ')}
               -> { wfPtrE S.empty e' } @-}
labelWFPtr :: (Ord p, Fractional p) => DSL p -> Int
           -> Int -> LDSL p Int -> LabelEnv p Int -> Proof
labelWFPtr e m0 m e' λ' = labelEElems e m0 M.empty m e' λ'


{-@ labelEIncrEnv :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
                  -> m:{Nat | m >= m0} -> e':LDSL p (Btwn 0 m)
                  -> λ':{LabelEnv p (Btwn 0 m) | labelE e m0 λ = (m,e',λ')}
                  -> MapGE λ' λ
                   / [size e] @-}
labelEIncrEnv :: (Ord p, Fractional p) => DSL p -> Int -> LabelEnv p Int
              -> Int -> LDSL p Int -> LabelEnv p Int -> (String -> Proof)
labelEIncrEnv e m0 λ m e' λ' x = case e of
  VAR s τ -> case M.lookup s λ of
    Nothing -> lookupLemma x λ -- x ∈ λ by hypothesis, so x ≠ s
    Just _ -> trivial
  CONST _ -> trivial
  BOOL  _ -> trivial

  UN op e1 -> case op of
    BoolToF -> labelEIncrEnv e1 m0 λ m1 e1' λ1 x
      where (m1,e1',λ1) = labelE e1 m0 λ
    ISZERO -> labelEIncrEnv (UN (EQLC zero) e1) m0 λ m e' λ' x
    EQLC _ -> labelEIncrEnv e1 m0 λ m1 e1' λ1 x
      where (m1,e1',λ1) = labelE e1 m0 λ
    _ -> labelEIncrEnv e1 m0 λ m1 e1' λ1 x
      where (m1,e1',λ1) = labelE e1 m0 λ

  BIN op e1 e2 -> case op of
    DIV -> labelEIncrEnv e1 m0 λ  m1 e1' λ1 x
        ?? labelEIncrEnv e2 m1 λ1 m2 e2' λ2 x
      where (m1,e1',λ1) = labelE e1 m0 λ
            (m2,e2',λ2) = labelE e2 m1 λ1
    EQL -> labelEIncrEnv (UN (EQLC zero) (BIN SUB e1 e2)) m0 λ m e' λ' x
    _ -> labelEIncrEnv e1 m0 λ  m1 e1' λ1 x
      ?? labelEIncrEnv e2 m1 λ1 m2 e2' λ2 x
      where (m1,e1',λ1) = labelE e1 m0 λ
            (m2,e2',λ2) = labelE e2 m1 λ1

  NIL _ -> trivial
  CONS e1 e2 -> labelEIncrEnv e1 m0 λ  m1 e1' λ1 x
             ?? labelEIncrEnv e2 m1 λ1 m2 e2' λ2 x
    where (m1,e1',λ1) = labelE e1 m0 λ
          (m2,e2',λ2) = labelE e2 m1 λ1


{-@ labelAIncrEnv :: a:Assertion p -> m0:Nat -> λ0:LabelEnv p (Btwn 0 m0)
                  -> m:{Nat | m >= m0} -> a':LAss p (Btwn 0 m)
                  -> λ:{LabelEnv p (Btwn 0 m) | labelA a m0 λ0 = (m,a',λ)}
                  -> MapGE λ λ0 @-}
labelAIncrEnv :: (Ord p, Fractional p) => Assertion p -> Int -> LabelEnv p Int
              -> Int -> LAss p Int -> LabelEnv p Int -> (String -> Proof)
labelAIncrEnv a m0 λ0 _m a' _λ x = case a of
  NZERO e1 -> case inferType e1 of
    Just _ -> labelEIncrEnv e1 m0 λ0 m e1' λ x where
      (m,e1',λ) = labelE e1 m0 λ0
  BOOLEAN e1 -> case inferType e1 of
    Just _ -> labelEIncrEnv e1 m0 λ0 m e1' λ x where
      (m,e1',λ) = labelE e1 m0 λ0
  EQA e1 e2 -> case inferType e1 of
    Just _ -> case inferType e2 of
      Just _ -> labelEIncrEnv e1 m0 λ0 m1 e1' λ1 x
             ?? labelEIncrEnv e2 m1 λ1 m2 e2' λ2 x where
         (m1,e1',λ1) = labelE e1 m0 λ0
         (m2,e2',λ2) = labelE e2 m1 λ1

{-@ labelAsIncrEnv :: st:Store p -> m0:Nat -> λ0:LabelEnv p (Btwn 0 m0)
                   -> m:{Nat | m >= m0} -> st':[LAss p (Btwn 0 m)]
                   -> λ:{LabelEnv p (Btwn 0 m) | labelAs st m0 λ0 = (m,st',λ)}
                   -> MapGE λ λ0 @-}
labelAsIncrEnv :: (Ord p, Fractional p) => Store p -> Int -> LabelEnv p Int
               -> Int -> [LAss p Int] -> LabelEnv p Int -> (String -> Proof)
labelAsIncrEnv store m0 λ0 _m store' _λ x = case store of
  [] -> trivial
  a:as -> labelAIncrEnv a  m0 λ0 m1 a'  λ1 x
       ?? labelAsIncrEnv as m1 λ1 m  as' λ x where
    (m1,a', λ1) = labelA a m0 λ0
    (m, as',λ)  = labelAs as m1 λ1

{-@ labelEElems :: e:TypedDSL p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
                -> m:{Nat | m >= m0} -> e':LDSL p (Btwn 0 m)
                -> λ':{LabelEnv p (Btwn 0 m) | labelE e m0 λ = (m,e',λ')}
                -> { S.isSubsetOf (elemsSet λ') (S.union (elemsSet λ) (wiresE e'))
                     && S.isSubsetOf (elemsSet λ) (elemsSet λ')
                     && wfPtrE (elemsSet λ) e' }
                 / [size e] @-}
labelEElems :: (Ord p, Fractional p) => DSL p -> Int -> LabelEnv p Int
            -> Int -> LDSL p Int -> LabelEnv p Int -> Proof
labelEElems e m0 λ m e' λ' = case e of
  VAR s τ -> case M.lookup s λ of
    Nothing -> trivial
    Just j -> elementLemma s j λ
  CONST _ -> trivial
  BOOL  _ -> trivial

  UN op e1 -> case op of
    BoolToF -> labelEElems e1 m0 λ m1 e1' λ1
      where (m1,e1',λ1) = labelE e1 m0 λ
    ISZERO -> labelEElems (UN (EQLC zero) e1) m0 λ m e' λ'
    EQLC _ -> labelEElems e1 m0 λ m1 e1' λ1
      where (m1,e1',λ1) = labelE e1 m0 λ
    _ -> labelEElems e1 m0 λ m1 e1' λ1
      where (m1,e1',λ1) = labelE e1 m0 λ

  BIN op e1 e2 -> case op of
    DIV -> labelEElems e1 m0 λ  m1 e1' λ1
        ?? labelEElems e2 m1 λ1 m2 e2' λ2
        ?? wfPtrEIncr (elemsSet λ1)
                      (elemsSet λ `S.union` wiresE e1')
                      e2'
      where (m1,e1',λ1) = labelE e1 m0 λ
            (m2,e2',λ2) = labelE e2 m1 λ1
    EQL -> labelEElems (UN (EQLC zero) (BIN SUB e1 e2)) m0 λ m e' λ'
    _ -> labelEElems e1 m0 λ  m1 e1' λ1
      ?? labelEElems e2 m1 λ1 m2 e2' λ2
      ?? wfPtrEIncr (elemsSet λ1)
                    (elemsSet λ `S.union` wiresE e1')
                    e2'
      where (m1,e1',λ1) = labelE e1 m0 λ
            (m2,e2',λ2) = labelE e2 m1 λ1

  NIL _ -> trivial
  CONS e1 e2 -> labelEElems e1 m0 λ  m1 e1' λ1
             ?? labelEElems e2 m1 λ1 m2 e2' λ2
             ?? wfPtrEIncr (elemsSet λ1)
                           (elemsSet λ `S.union` wiresE e1')
                           e2'
    where (m1,e1',λ1) = labelE e1 m0 λ
          (m2,e2',λ2) = labelE e2 m1 λ1

{-@ labelAElems :: a:Assertion p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
                -> m:{Nat | m >= m0} -> a':LAss p (Btwn 0 m)
                -> λ':{LabelEnv p (Btwn 0 m) | labelA a m0 λ = (m,a',λ')}
                -> { S.isSubsetOf (elemsSet λ') (S.union (elemsSet λ) (wiresA a'))
                     && S.isSubsetOf (elemsSet λ) (elemsSet λ')
                     && wfPtrA (elemsSet λ) a' } @-}
labelAElems :: (Ord p, Fractional p) => Assertion p -> Int -> LabelEnv p Int
            -> Int -> LAss p Int -> LabelEnv p Int -> Proof
labelAElems a m0 λ m a' λ' = case a of
  NZERO e1 -> case inferType e1 of
    Just _ -> labelEElems e1 m0 λ m1 e1' λ1 where
      (m1,e1',λ1) = labelE e1 m0 λ
  BOOLEAN e1 -> case inferType e1 of
    Just _ -> labelEElems e1 m0 λ m1 e1' λ1 where
      (m1,e1',λ1) = labelE e1 m0 λ
  EQA e1 e2 -> case inferType e1 of
    Just _ -> case inferType e2 of
      Just _ -> labelEElems e1 m0 λ  m1 e1' λ1
             ?? labelEElems e2 m1 λ1 m2 e2' λ2
             ?? wfPtrEIncr (elemsSet λ1) (S.union (elemsSet λ) (wiresE e1')) e2'
        where
        (m1,e1',λ1) = labelE e1 m0 λ
        (m2,e2',λ2) = labelE e2 m1 λ1

{-@ labelAsElems :: as:Store p -> m0:Nat -> λ:LabelEnv p (Btwn 0 m0)
                 -> m:{Nat | m >= m0} -> as':[LAss p (Btwn 0 m)]
                 -> λ':{LabelEnv p (Btwn 0 m) | labelAs as m0 λ = (m,as',λ')}
                 -> { S.isSubsetOf (elemsSet λ') (S.union (elemsSet λ) (wiresAs as'))
                      && S.isSubsetOf (elemsSet λ) (elemsSet λ')
                      && wfPtrAs (elemsSet λ) as'} @-}
labelAsElems :: (Ord p, Fractional p) => Store p -> Int -> LabelEnv p Int
             -> Int -> [LAss p Int] -> LabelEnv p Int -> Proof
labelAsElems store m0 λ _m store' _λ' = case store of
  [] -> trivial
  a:as -> labelAElems  a  m0 λ  m1 a'  λ1
       ?? labelAsElems as m1 λ1 m  as' λ'
       ?? wfPtrAsIncr (elemsSet λ1) (S.union (elemsSet λ) (wiresA a')) as'
    where
    (m1,a', λ1) = labelA a m0 λ
    (m ,as',λ') = labelAs as m1 λ1
