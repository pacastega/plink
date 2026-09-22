{-# LANGUAGE CPP #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module AssertionLemmas where

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import qualified Data.Set as S

import Utils
import TypeAliases

import Constraints
import DSL
import Label
import WitnessGeneration

import MapLemmas
import SetLemmas
import Language.Haskell.Liquid.ProofCombinators


{-@ labelNZ :: m0:Nat -> e1:DSL p -> λ:LabelEnv p (Btwn 0 m0)

            -> m1:{Int | m1 >= m0}
            -> e1':LDSL p (Btwn 0 m1)
            -> λ1:{LabelEnv p (Btwn 0 m1) | label' e1 m0 λ  = (m1, e1', λ1)}

            -> m:{Int | m >= m1}
            -> a':LAss p (Btwn 0 m)
            -> λ':{LabelEnv p (Btwn 0 m) |
                            labelAssertion (NZERO e1) m0 λ = (m, a', λ')}
            -> w:{Btwn 0 m | a' = LNZERO e1' w} @-}
labelNZ :: (Num p, Ord p) => Int -> DSL p -> LabelEnv p Int
        -> Int -> LDSL p Int -> LabelEnv p Int
        -> Int -> LAss p Int -> LabelEnv p Int
        -> Int
labelNZ m0 e1 λ m1 e1' λ1 m a' λ' = case a' of LNZERO _ w -> w
