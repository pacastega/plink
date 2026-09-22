{-# LANGUAGE CPP #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
module FundamentalTheoremLemmas where

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

import FundamentalTheorem hiding (foo, barOp)

import Language.Haskell.Liquid.ProofCombinators


{-@ fundamentalThmA1' :: m0:Nat -> a:Assertion p
                     -> ρ:{NameValuation p | holds a ρ}

                     -> m:{Nat | m0 <= m}
                     -> λ0:LabelEnv p (Btwn 0 m0)
                     -> σ0:WireValuation p m0
                     -> Agree λ0 ρ σ0

                     -> a':{LAss p (Btwn 0 m) | freshA a' σ0}
                     -> λ:{LabelEnv p (Btwn 0 m) |
                              labelAssertion a m0 λ0 = (m, a', λ)}

                     -> (σ::{σ:WireValuation p m | coherentA m a' σ
                                                && M.keysSet σ =
                                                   S.union (M.keysSet σ0) (wiresA a')},
                         x:{String | M.member x λ} ->
                            { v:() | M.lookup x ρ = M.lookup (M.lookup' x λ) σ }) @-}
fundamentalThmA1' :: (Fractional p, Ord p) => Int -> Assertion p
                 -> NameValuation p

                 -> Int -> LabelEnv p Int -> WireValuation p -> (String -> Proof)
                 -> LAss p Int -> LabelEnv p Int

                 -> (WireValuation p, String -> Proof)
fundamentalThmA1' m0 a ρ m λ0 σ0 π0 a' λ = case a of
  NZERO e1 ->
              fakeΣ m0 ρ m σ0 a' λ
    --           (σ',π')
    --           --TODO: this π does not work (σ is updated!)
    --           ? evalWireIncr m e1' σ σ' hσ
    --           ? evalWireScalar m e1' σ'
    --           ? coherentEIncr m e1' σ σ' hσ
    -- where

    -- (m1,e1',λ1) = label' e1 m0 λ0

    -- v1 = case eval e1 ρ of Just v -> v
    -- v1' = case v1 of VF v -> v

    -- LNZERO _ w = a'

    -- (σ,π) = fundamentalThmE1 m0 e1 ρ m1 m λ0 σ0 π0 e1' λ1 v1
    -- σ' = M.insert w (1/v1') σ

    -- {-@ hσ :: MapGE σ' σ @-}
    -- hσ j = if j == w then ltLemma 0 m1 (M.keysSet σ) j else () ? σ ? σ'

    -- {-@ π' :: Agree λ ρ σ' @-}
    -- π' :: String -> Proof
    -- π' x = π x ? notElemLemma x w λ1

  BOOLEAN e1 -> fakeΣ m0 ρ m σ0 a' λ
    --             (σ,π) ? evalWireScalar m e1' σ where
    -- (m1,e1',λ1) = label' e1 m0 λ0
    -- v1 = case eval e1 ρ of Just v -> v
    -- (σ,π) = fundamentalThmE1 m0 e1 ρ m1 m λ0 σ0 π0 e1' λ v1

  EQA e1 e2 ->
               -- fakeΣ m0 ρ m σ0 a' λ
               (σ2
               ? evalWireScalar m e1' σ1            -- σ1(e1') = σ1[i1]
               ? evalWireIncr m e1' σ1 σ2 σ2_ge_σ1  -- σ2(e1') = σ1(e1') since σ2 ≥ σ1
               ? coherentEIncr m e1' σ1 σ2 σ2_ge_σ1 -- σ2 ⊢ e1' since σ2 ≥ σ1
               ? evalWireScalar m e2' σ2            -- σ2(e2') = σ2[i2]
               -- ? liquidAssert (coherentE m e1' σ2)
               -- ? liquidAssert (coherentE m e2' σ2)
               -- ? liquidAssert (v1 == v2)
               -- ? liquidAssert (evalWire m e1' σ1 == v1)
               ? liquidAssert (evalWire m e1' σ2 == v1))
               -- ? liquidAssert (evalWire m e2' σ2 == v2)
               ,π2)
    where

    (m1,e1',λ1) = label' e1 m0 λ0
    (m2,e2',λ2) = label' e2 m1 λ1

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




-- {-@ fundamentalThmA2' :: m0:Nat -> a:Assertion p
--                      -> ρ:NameValuation p

--                      -> m:{Nat | m0 <= m}
--                      -> a':{LAss p (Btwn 0 m) | isJust (tyEnvA a' M.MTip)}
--                      -> λ:{LabelEnv p (Btwn 0 m) |
--                               labelAssertion a m0 M.MTip = (m, a', λ)}

--                      -> σ:{WireValuation p m | closedAssertion m σ a'
--                                             && coherentA m a' σ}
--                      -> Agree λ ρ σ

--                      -> { holds a ρ } @-}
-- fundamentalThmA2' :: (Fractional p, Ord p) => Int -> Assertion p
--                  -> NameValuation p

--                  -> Int -> LAss p Int -> LabelEnv p Int

--                  -> WireValuation p -> (String -> Proof)

--                  -> Proof
-- fundamentalThmA2' m0 a ρ m a' λ σ π = case a of
--   NZERO e1 -> wtE ?? wf
--     ?? evalWireUnique m0 m1 e1 ρ λ0 m e1' λ1 σ π v1 γ0 γ1 h_bool where
--     λ0 = M.MTip

--     γ0 :: TyEnv' γ0
--     γ0 = M.MTip

--     {-@ wtE :: { wellTyped e1 } @-}
--     wtE = case inferType e1 of Just _ -> trivial

--     (m1,e1',λ1) = wtE ?? label' e1 m0 λ0

--     wf = labelWF e1 m0 λ0 m1 e1' λ1
--     wt = labelTyped e1 m0 λ0 m1 e1' λ1

--     γ1 = wt ?? case tyEnvE e1' γ0 of Just g -> g

--     v1 = evalWire m1 e1' σ

--     {-@ h_bool :: j:{Btwn 0 m | S.member j (elemsSet λ)
--                              && M.lookup j γ1 = Just TBool}
--                -> { boolean (M.lookup' j σ) } @-}
--     h_bool j = labelElems e1 m0 λ0 m1 e1' λ1
--             ?? liquidAssert (S.isSubsetOf (elemsSet λ1) (S.union (elemsSet λ0) (wiresE e1')))
--             ?? wt
--             ?? booleanProof' m σ e1' γ0 γ1 j

--   BOOLEAN e1 -> undefined
--   EQA e1 e2 -> undefined


--   -- wf ?? evalWireUnique m0 m e ρ λ0 m e' λ σ π v γ0 γ h_bool
--   -- where
--   --   λ0 = M.MTip

--   --   γ0 :: TyEnv' γ0
--   --   γ0 = M.MTip

--   --   wf = labelWF e m0 λ0 m e' λ
--   --   wt = labelTyped e m0 λ0 m e' λ

--   --   γ = wt ?? case tyEnvE e' γ0 of Just g -> g

--   --   {-@ h_bool :: j:{Btwn 0 m | S.member j (elemsSet λ)
--   --                            && M.lookup j γ = Just TBool}
--   --              -> { boolean (M.lookup' j σ) } @-}
--   --   h_bool j = labelElems e m0 λ0 m e' λ
--   --           ?? liquidAssert (S.isSubsetOf (elemsSet λ) (S.union (elemsSet λ0) (wiresE e')))
--   --           ?? wt
--   --           ?? booleanProof' m σ e' γ0 γ j


-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1


{-@ assume fakeΣ :: m0:Nat -> ρ:NameValuation p -> m:{Nat | m0 <= m}
                 -> σ0:WireValuation p m0
                 -> a':LAss p (Btwn 0 m)
                 -> λ:LabelEnv p (Btwn 0 m)
                 -> (σ::{σ:WireValuation p m | coherentA m a' σ
                                            && M.keysSet σ =
                                               S.union (M.keysSet σ0) (wiresA a')},
                    x:{String | M.member x λ} ->
                       { v:() | M.lookup x ρ = M.lookup (M.lookup' x λ) σ }) @-}
fakeΣ :: Int -> NameValuation p -> Int -> WireValuation p -> LAss p Int -> LabelEnv p Int
      -> (WireValuation p, String -> Proof)
fakeΣ m0 ρ m σ0 a' λ = (M.empty, \_ -> ())
