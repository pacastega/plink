{-# LANGUAGE CPP #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
module FundamentalTheorem.FundamentalTheoremLemmas where

import Constraints
import TypeAliases
import DSL
import Semantics
import Semantics2 hiding (foo, barOp)
import Label
import WitnessGeneration

import Utils

import BooleanProof hiding (foo, barOp)

import qualified Data.Set as S

#if LiquidOn
import qualified Liquid.Data.Map as M
#else
import qualified Data.Map as M
import qualified MapFunctions as M
#endif

import MapLemmas
import SetLemmas
import LabelingProof.LabelingLemmas
import LabelingProof.AgreeLemma
import LabelingProof.RecursiveLemmas hiding (foo, barOp)
import WitnessGenProof.UniquenessLemmas
import WitnessGenProof.SemanticsLemmas
import WitnessGenProof.WitnessGenLemmas
import AssertionLemmas
import WitnessGenProof.Soundness
import WitnessGenProof.Completeness
import WitnessGenProof.Uniqueness

import Language.Haskell.Liquid.ProofCombinators


{-@ fundamentalThmE1 :: m0:Nat -> e:TypedDSL p
                     -> ρ:NameValuation p

                     -> m1:{Nat | m0 <= m1} -> m:{Nat | m1 <= m}
                     -> λ0:LabelEnv p (Btwn 0 m0)
                     -> σ0:WireValuation p m0
                     -> Agree λ0 ρ σ0

                     -> e':{LDSL p (Btwn 0 m1) | freshE e' σ0}
                     -> λ:{LabelEnv p (Btwn 0 m1) | labelE e m0 λ0 = (m1, e', λ)}

                     -> v:{DSLValue p | eval e ρ = Just v}

                     -> (σ::{σ:WireValuation p m1 | Just σ = witnessGenE m ρ σ0 e'
                                                && closedExpr m σ e'
                                                && coherentE m e' σ
                                                && evalWire m e' σ = v
                                                && M.keysSet σ =
                                            S.union (M.keysSet σ0) (wiresE e')},
                         x:{String | M.member x λ} ->
                            { v:() | M.lookup x ρ = M.lookup (M.lookup' x λ) σ }) @-}
fundamentalThmE1 :: (Fractional p, Ord p) => Int -> DSL p
                 -> NameValuation p

                 -> Int -> Int -> LabelEnv p Int -> WireValuation p
                 -> (String -> Proof)
                 -> LDSL p Int -> LabelEnv p Int
                 -> DSLValue p

                 -> (WireValuation p, String -> Proof)
fundamentalThmE1 m0 e ρ m1 m λ0 σ0 π e' λ v =
  (σ ? σ_closed ? sound ? σ_eq_wg ? σ_eval,
   agreeLemma m0 m1 e ρ λ0 σ0 π λ e' σ)
  where
    wf = labelWF e m0 λ0 m1 e' λ
    wt = labelTyped e m0 λ0 m1 e' λ
    sound = wf ?? wt ?? wgLemma m1 m ρ σ0 e' ?? wgSoundE m ρ σ0 e' σ
    σ = wf ?? wgCompleteE m0 e ρ v λ0 σ0 π m1 e' λ
    σ_eq_wg = wgKeysSet m1 ρ σ0 e' σ
    σ_closed = wgClosed m1 ρ σ0 e' σ
    σ_eval = evalWireLemma m1 m e' σ

{-@ fundamentalThmA1 :: m0:Nat -> a:Assertion p
                     -> ρ:{NameValuation p | holds a ρ}

                     -> m1:{Nat | m0 <= m1} -> m:{Nat | m1 <= m}
                     -> λ0:LabelEnv p (Btwn 0 m0)
                     -> σ0:WireValuation p m0
                     -> Agree λ0 ρ σ0

                     -> a':{LAss p (Btwn 0 m1) | freshA a' σ0}
                     -> λ:{LabelEnv p (Btwn 0 m1) |
                              labelA a m0 λ0 = (m1, a', λ)}

                     -> (σ::{σ:WireValuation p m1 | Just σ = witnessGenA m ρ σ0 a'
                                                && coherentA m a' σ
                                                && M.keysSet σ =
                                                   S.union (M.keysSet σ0) (wiresA a')},
                         x:{String | M.member x λ} ->
                            { v:() | M.lookup x ρ = M.lookup (M.lookup' x λ) σ }) @-}
fundamentalThmA1 :: (Fractional p, Ord p) => Int -> Assertion p
                 -> NameValuation p

                 -> Int -> Int -> LabelEnv p Int -> WireValuation p
                 -> (String -> Proof)
                 -> LAss p Int -> LabelEnv p Int

                 -> (WireValuation p, String -> Proof)
fundamentalThmA1 m0 a ρ m1 m λ0 σ0 π0 a' λ = case a of
  NZERO e1 -> (σ',π')
              ? evalWireIncr m e1' σ σ' hσ
              ? evalWireScalar m e1' σ'
              ? coherentEIncr m e1' σ σ' hσ
    where

    (m1,e1',λ1) = labelE e1 m0 λ0

    v1 = case eval e1 ρ of Just v -> v
    v1' = case v1 of VF v -> v

    LNZERO _ w = a'

    (σ,π) = fundamentalThmE1 m0 e1 ρ m1 m λ0 σ0 π0 e1' λ1 v1
    σ' = evalWireScalar m e1' σ
      ?? M.insert w (1/v1') σ

    {-@ hσ :: MapGE σ' σ @-}
    hσ j = if j == w then ltLemma 0 m1 (M.keysSet σ) j else () ? σ ? σ'

    {-@ π' :: Agree λ ρ σ' @-}
    π' :: String -> Proof
    π' x = π x ? notElemLemma x w λ1

  BOOLEAN e1 -> (σ,π) ? evalWireScalar m e1' σ where
    (m1,e1',λ1) = labelE e1 m0 λ0
    v1 = case eval e1 ρ of Just v -> v
    (σ,π) = fundamentalThmE1 m0 e1 ρ m1 m λ0 σ0 π0 e1' λ v1

  EQA e1 e2 -> ( σ2
               , π2)
               ? evalWireScalar m e1' σ1            -- σ1(e1') = σ1[i1]
               ? evalWireIncr m e1' σ1 σ2 σ2_ge_σ1  -- σ2(e1') = σ1(e1') since σ2 ≥ σ1
               ? coherentEIncr m e1' σ1 σ2 σ2_ge_σ1 -- σ2 ⊢ e1' since σ2 ≥ σ1
               ? evalWireScalar m e2' σ2            -- σ2(e2') = σ2[i2]
               ? liquidAssert (evalWire m e1' σ2 == v1)
    where

    (m1,e1',λ1) = labelE e1 m0 λ0
    (m2,e2',λ2) = labelE e2 m1 λ1

    {-@ fresh2 :: { freshE e2' σ1 } @-}
    fresh2 = disjLemma 0 m1 m2 (M.keysSet σ1) (wiresE e2')

    v1 = case eval e1 ρ of Just v -> v
    v2 = case eval e2 ρ of Just v -> v

    (σ1,π1) = fundamentalThmE1 m0 e1 ρ m1 m λ0 σ0 π0 e1' λ1 v1
    (σ2,π2) = fresh2 ?? fundamentalThmE1 m1 e2 ρ m2 m λ1 σ1 π1 e2' λ2 v2

    {-@ σ2_ge_σ1 :: MapGE σ2 σ1 @-}
    σ2_ge_σ1 :: Int -> Proof
    σ2_ge_σ1 = labelWF e2 m1 λ1 m2 e2' λ2 ?? wgIncr m ρ σ1 e2' σ2



--------------------------------------------------------------------------------




{-@ fundamentalThmA2 :: m0:Nat -> a:Assertion p
                     -> ρ:NameValuation p

                     -> m1:{Nat | m0 <= m1} -> m:{Nat | m1 <= m}
                     -> λ0:LabelEnv p (Btwn 0 m0)

                     -> a':LAss p (Btwn 0 m1)
                     -> λ:{LabelEnv p (Btwn 0 m1) |
                              labelA a m0 λ0 = (m1, a', λ)}

                     -> σ:{WireValuation p m | closedAssertion m σ a'
                                             && coherentA m a' σ}
                     -> Agree λ ρ σ

                     -> γ0:TyEnv' (Btwn 0 m0)
                     -> γ:{TyEnv' (Btwn 0 m1) | Just γ = tyEnvA a' γ0}
                     -> ( j:{Btwn 0 m1 | S.member j (elemsSet λ)
                                      && M.lookup j γ = Just TBool}
                            -> { boolean (M.lookup' j σ) } )

                     -> { holds a ρ } @-}
fundamentalThmA2 :: (Fractional p, Ord p) => Int -> Assertion p
                 -> NameValuation p

                 -> Int -> Int -> LabelEnv p Int

                 -> LAss p Int -> LabelEnv p Int
                 -> WireValuation p -> (String -> Proof)

                 -> TyEnv' Int -> TyEnv' Int -> (Int -> Proof)

                 -> Proof
fundamentalThmA2 m0 a ρ m1 m λ0 a' λ σ π γ0 γ h_bool = case a of
  NZERO e1 -> evalWireUnique m0 m e1 ρ λ0 me1 e1' λ1 σ π v1 γ0 γ1 h_bool1
    where
    {-@ wtE :: { wellTyped e1 } @-}
    wtE = case inferType e1 of Just _ -> trivial

    (me1,e1',λ1) = wtE ?? labelE e1 m0 λ0

    LNZERO _ w = a'

    _wf = labelWF e1 m0 λ0 me1 e1' λ1

    γ1 = case tyEnvE e1' γ0 of Just g -> g

    v1 = evalWire m e1' σ
    _v1' = case v1 of VF v -> v

    {-@ h_bool1 :: j:{Btwn 0 m1 | S.member j (elemsSet λ)
                              && M.lookup j γ1 = Just TBool}
                -> { boolean (M.lookup' j σ) } @-}
    h_bool1 j = keyLemma j TBool γ1      -- j ∈ γ1
              ? lookupLemma j γ1         -- lookup γ1 j == Just (γ1[j])
              ? insertICIncr w TF γ1 γ j -- γ[j] == γ1[j]
              ? lookupLemma j γ          -- lookup γ j == Just (γ[j])
              ? h_bool j

  BOOLEAN e1 -> evalWireUnique m0 m e1 ρ λ0 me1 e1' λ1 σ π v1 γ0 γ h_bool
    where
    {-@ wtE :: { wellTyped e1 } @-}
    wtE = case inferType e1 of Just _ -> trivial

    (me1,e1',λ1) = wtE ?? labelE e1 m0 λ0

    _wf = labelWF e1 m0 λ0 me1 e1' λ1

    v1 = evalWire m e1' σ
    _v1' = case v1 of VF v -> v

  EQA e1 e2 -> evalWireUnique m0  m e1 ρ λ0 me1 e1' λ1 σ π1 v1 γ0 γ1 h_bool1
             ? evalWireUnique me1 m e2 ρ λ1 me2 e2' λ2 σ π  v2 γ1 γ  h_bool
    where
    {-@ wtE1 :: { wellTyped e1 } @-}
    wtE1 = case inferType e1 of Just _ -> trivial

    {-@ wtE2 :: { wellTyped e2 } @-}
    wtE2 = case inferType e2 of Just _ -> trivial

    (me1,e1',λ1) = wtE1 ?? labelE e1 m0  λ0
    (me2,e2',λ2) = wtE2 ?? labelE e2 me1 λ1

    _wf1 = labelWF e1 m0  λ0 me1 e1' λ1
    _wf2 = labelWF e2 me1 λ1 me2 e2' λ2

    γ1 = case tyEnvE e1' γ0 of Just g -> g

    v1 = evalWire m e1' σ
    v2 = evalWire m e2' σ
    _v1' = case v1 of VF v -> v
    _v2' = case v2 of VF v -> v

    {-@ π1 :: Agree λ1 ρ σ @-}
    π1 x = labelEIncrEnv e2 me1 λ1 me2 e2' λ2 x ?? π x

    {-@ h_bool1 :: j:{Btwn 0 me1 | S.member j (elemsSet λ1)
                              && M.lookup j γ1 = Just TBool}
                -> { boolean (M.lookup' j σ) } @-}
    h_bool1 j = keyLemma j  TBool γ1  -- j ∈ γ1
             ?? lookupLemma j γ1      -- lookup γ1 j == Just (γ1[j])
             ?? tyEnvEIncr e2' γ1 γ j -- γ[j] == γ1[j]
             ?? lookupLemma j γ       -- lookup γ j == Just (γ[j])
             ?? labelEElems e2 me1 λ1 me2 e2' λ
             ?? h_bool j


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
