{-# LANGUAGE CPP #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--save" @-}
module FundamentalTheorem.FundamentalTheorem where

import Constraints
import TypeAliases
import DSL
import Semantics
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
import WitnessGenProof.WitnessGenLemmas
import LabelingProof.AgreeLemma
import LabelingProof.RecursiveLemmas hiding (foo, barOp)
import WitnessGenProof.SemanticsLemmas
import WitnessGenProof.UniquenessLemmas
import WitnessGenProof.Soundness
import WitnessGenProof.Completeness
import WitnessGenProof.Uniqueness
import AssertionLemmas

import FundamentalTheorem.FundamentalTheoremLemmas hiding (foo, barOp)

-- import FundamentalTheorem.NewLemmas hiding (foo, barOp)
-- import FundamentalTheorem.NewerLemmas hiding (foo, barOp)
-- import FundamentalTheorem.NewBooleanProof hiding (foo, barOp)

import Language.Haskell.Liquid.ProofCombinators



--------------------------------------------------------------------------------

{-@ fundamentalThmS1 :: m0:Nat -> st:Store p
                     -> ρ:{NameValuation p | holdsAll st ρ}

                     -> m1:{Nat | m0 <= m1} -> m:{Nat | m1 <= m}
                     -> λ0:LabelEnv p (Btwn 0 m0)
                     -> σ0:WireValuation p m0
                     -> Agree λ0 ρ σ0

                     -> st':{[a':LAss p (Btwn 0 m1)] | wfAs st' && freshAs st' σ0}
                     -> λ:{LabelEnv p (Btwn 0 m1) | labelAs st m0 λ0 = (m1, st', λ)}

                     -> (σ::{σ:WireValuation p m1 | Just σ = witnessGenAs m ρ σ0 st'
                                               && coherentAs m σ st'
                                               && M.keysSet σ =
                                                  S.union (M.keysSet σ0) (wiresAs st')},
                         x:{String | M.member x λ} ->
                            { v:() | M.lookup x ρ = M.lookup (M.lookup' x λ) σ }) @-}
fundamentalThmS1 :: (Fractional p, Ord p)
                 => Int -> Store p -> NameValuation p
                 -> Int -> Int -> LabelEnv p Int -> WireValuation p
                 -> (String -> Proof)

                 -> [LAss p Int] -> LabelEnv p Int
                 -> (WireValuation p, String -> Proof)
fundamentalThmS1 m0 st ρ m1 m λ0 σ0 π0 st' λ = case st of
  [] -> (σ0, π0)
  a:as -> h_σ ?? (σ,π)
    where
      (me1,a',λ1) = labelA a m0 λ0
      (_,as',_) = labelAs as me1 λ1

      (σ1,π1) = fundamentalThmA1 m0 a ρ me1 m λ0 σ0 π0 a'  λ1
      h_σ1 = wgALemma me1 m ρ σ0 a' -- σ1 = wgA me1 ρ σ a' = wgA m ρ σ a'

      (σ,π) = fundamentalThmS1 me1 as ρ m1 m λ1 (σ1 ? h_σ1) π1 as' λ

      {-@ σ_ge_σ1 :: MapGE σ σ1 @-}
      σ_ge_σ1 :: Int -> Proof
      σ_ge_σ1 = wgAsIncr m ρ σ1 as' σ

      {-@ h_σ :: { coherentA m a' σ } @-}
      h_σ = wgAClosed m ρ σ0 a' σ1
         ?? coherentAIncr m a' σ1 σ σ_ge_σ1


{-@ fundamentalThmS2 :: m0:Nat -> st:Store p
                     -> ρ:NameValuation p

                     -> m1:{Nat | m0 <= m1} -> m:{Nat | m1 <= m}
                     -> λ0:LabelEnv p (Btwn 0 m0)

                     -> st':[LAss p (Btwn 0 m1)]
                     -> λ:{LabelEnv p (Btwn 0 m1) |
                              labelAs st m0 λ0 = (m1, st', λ)}

                     -> σ:{WireValuation p m | closedAssertions m σ st'
                                            && coherentAs m σ st'}
                     -> Agree λ ρ σ

                     -> γ0:TyEnv' (Btwn 0 m0)
                     -> γ:{TyEnv' (Btwn 0 m) | Just γ = tyEnvAs st' γ0}
                     -> ( j:{Btwn 0 m1 | S.member j (elemsSet λ)
                                      && M.lookup j γ = Just TBool}
                            -> { boolean (M.lookup' j σ) } )

                     -> { holdsAll st ρ } @-}
fundamentalThmS2 :: (Fractional p, Ord p) => Int -> Store p
                 -> NameValuation p

                 -> Int -> Int -> LabelEnv p Int

                 -> [LAss p Int] -> LabelEnv p Int
                 -> WireValuation p
                 -> (String -> Proof)

                 -> TyEnv' Int -> TyEnv' Int -> (Int -> Proof)

                 -> Proof
fundamentalThmS2 m0 st ρ m1 m λ0 st' λ σ π γ0 γ h_bool = case st of
  [] -> trivial
  a:as -> holdsA ? holdsAs where
    (m1,a', λ1) = labelA a m0 λ0
    (m',as',λ') = labelAs as m1 λ1

    γ1 = case tyEnvA a' γ0 of Just g -> g

    holdsA = liquidAssert (closedAssertion m σ a')
          ?? fundamentalThmA2 m0 a ρ m1 m λ0 a' λ1 σ π1 γ0 γ1 h_bool1
    holdsAs = fundamentalThmS2 m1 as ρ m' m λ1 as' λ σ π γ1 γ h_bool

    {-@ π1 :: Agree λ1 ρ σ @-}
    π1 :: String -> Proof
    π1 x = labelAsIncrEnv as m1 λ1 m' as' λ' x ?? π x

    {-@ h_bool1 :: j:{Btwn 0 m1 | S.member j (elemsSet λ1)
                               && M.lookup j γ1 = Just TBool}
                -> { boolean (M.lookup' j σ) } @-}
    h_bool1 :: Int -> Proof
    h_bool1 j = keyLemma j TBool γ1
             ?? lookupLemma j γ1
             ?? tyEnvAsIncr as' γ1 γ j
             ?? lookupLemma j γ
             ?? labelAsElems as m1 λ1 m' as' λ'
             ?? h_bool j


{-@ fundamentalThm1 :: e:TypedDSL p -> st:Store p -> v:DSLValue p
                    -> ρ:{NameValuation p | eval e ρ = Just v && holdsAll st ρ}

                    -> m:Nat
                    -> e':LDSL p (Btwn 0 m)
                    -> st':[LAss p Int]

                    -> λ:{LabelEnv p (Btwn 0 m) | label e st = (m,e',st',λ)}

                    -> (σ::{σ:WireValuation p m | coherentE m e' σ
                                               && coherentAs m σ st'
                                               && evalWire m e' σ = v},
                        x:{String | M.member x λ} ->
                           { v:() | M.lookup x ρ = M.lookup (M.lookup' x λ) σ }) @-}
fundamentalThm1 :: (Fractional p, Ord p) => DSL p -> Store p -> DSLValue p
                -> NameValuation p -> Int -> LDSL p Int -> [LAss p Int]
                -> LabelEnv p Int
                -> (WireValuation p, String -> Proof)
fundamentalThm1 e st v ρ m e'' st'' λ = (σ2 ? st'_closed, π2) where
  m0 = 0
  σ0 = M.MTip
  λ0 = M.MTip

  (m1,st',λ1) = labelAs st m0 λ0
  (m2,e',λ2) = labelE e m1 λ1

  (σ1,π1) = labelAsWF st m0 λ0 m1 st' λ1
         ?? fundamentalThmS1 m0 st ρ m1 m λ0 σ0 (const trivial) st' λ1
  (σ2,π2) = disjLemma m0 m1 m2 (M.keysSet σ1) (wiresE e')
         ?? labelEElems e m1 λ1 m2 e' λ2
         ?? fundamentalThmE1 m1 e ρ m2 m λ1 σ1 π1 e' λ2 v

  wfE = labelTyped e m1 λ1 m2 e' λ2
     ?? labelWF    e m1 λ1 m2 e' λ2

  σ2_ge_σ1 = wgEIncr m ρ σ1 e' σ2

  st'_closed = wfE
             ? wgAsClosed m ρ σ0 st' σ1            -- wires(st') are bound in σ1
             ? coherentAsIncr m st' σ1 σ2 σ2_ge_σ1 -- wires(st') are bound in σ2

{-@ fundamentalThm2 :: e:TypedDSL p -> st:Store p -> v:DSLValue p
                    -> ρ:NameValuation p

                    -> m:Nat
                    -> e':LDSL p (Btwn 0 m)
                    -> st':[LAss p Int]

                    -> λ:{LabelEnv p (Btwn 0 m) | label e st = (m,e',st',λ)}
                    -> σ:{WireValuation p m | closedExpr m σ e'
                                           && coherentE m e' σ

                                           && closedAssertions m σ st'
                                           && coherentAs m σ st'
                                           && evalWire m e' σ = v}
                    -> Agree λ ρ σ

                    -> γ:{TyEnv' (Btwn 0 m) | Just γ = tyEnvPr e' st' M.MTip}

                    -> { eval e ρ = Just v
                        && holdsAll st ρ } @-}
fundamentalThm2 :: (Fractional p, Ord p) => DSL p -> Store p -> DSLValue p
                -> NameValuation p -> Int -> LDSL p Int -> [LAss p Int]
                -> LabelEnv p Int
                -> WireValuation p -> (String -> Proof)
                -> TyEnv' Int -> Proof
fundamentalThm2 e st v ρ m e'' st'' λ σ π γ = h_holds ? h_eval where
  m0 = 0
  -- σ0 = M.MTip
  λ0 = M.MTip

  γ0 :: TyEnv' Int
  γ0 = M.MTip

  (m1,st',λ1) = labelAs st m0 λ0
  (m2,e',λ2) = labelE e m1 λ1

  h_holds = labelAsWF st m0 λ0 m1 st' λ1
         ?? fundamentalThmS2 m0 st ρ m1 m λ0 st' λ1 σ π1 γ0 γ1 h_bool1
  h_eval = labelWF e m1 λ1 m2 e' λ2
        ?? evalWireUnique m1 m e ρ λ1 m2 e' λ2 σ π v γ1 γ2 h_bool2

  wtE = labelTyped e m1 λ1 m2 e' λ2

  γ1 = --tyEnvPr1 m0 m1 m2 e' st' γ0 γ ?? --TODO: maybe remove this
       case tyEnvAs st' γ0 of Just g -> g
  γ2 = γ

  {-@ π1 :: Agree λ1 ρ σ @-}
  π1 :: String -> Proof
  π1 x = labelEIncrEnv e m1 λ1 m2 e' λ x ?? π x

  {-@ h_bool1 :: j:{Btwn 0 m | S.member j (elemsSet λ1) && M.lookup j γ1 = Just TBool}
              -> { boolean (M.lookup' j σ) } @-}
  h_bool1 :: Int -> Proof
  h_bool1 j = keyLemma j TBool γ1 -- j ∈ keys(γ1)
           -- and keys(γ1) = wires(st') ∪ ptrs(st') ∪ keys(γ0)
           --              = wires(st') ∪ ptrs(st')
           -- by postcond of tyEnvAs

           ?? labelAsElems st m0 λ0 m1 st' λ1 -- elems(λ0) ⊨ st', which implies
           ?? wfPtrAsLemma (elemsSet λ0) st'  -- ptrs(st') ⊆ wires(st') ∪ elems(λ0)
                                              --           = wires(st')

           ?? booleanProofAs' m σ st' γ0 γ1 j

  {-@ h_bool2 :: j:{Btwn 0 m | S.member j (elemsSet λ2) && M.lookup j γ2 = Just TBool}
              -> { boolean (M.lookup' j σ) } @-}
  h_bool2 :: Int -> Proof
  h_bool2 j = if S.member j (wiresE e')
              then wtE ?? booleanProofE m σ e' γ1 γ2 j
              else labelEElems e m1 λ1 m2 e' λ2 -- elems(λ2) ⊆ elems(λ1) ∪ wires(e')
                -- and, since j ∉ wires(e'), j ∈ elems(λ1)                   (A)

                ?? keyLemma j TBool γ2 -- γ2[j] = TBool ⇒ j ∈ keys(γ2)

                -- keys(γ2) = keys(γ1) ∪ wires(e') ∪ ptrs(e') by postcond of tyEnvE
                ?? wfPtrELemma (elemsSet λ1) e' -- ptrs(e') ⊆ wires(e') ∪ elems(λ1)
                -- so in particular j ∈ keys(γ2) ⊆ keys(γ1) ∪ wires(e') ∪ elems(λ1)
                -- but, since j ∉ wires(e'),
                -- j ∈ keys(γ1) ∪ elems(λ1)

                ?? labelAsElems st m0 λ0 m1 st' λ1 -- elems(λ1) ⊆ elems(λ0) ∪ wires(st')
                -- but elems(λ0) = elems(∅) = ∅
                -- so j ∈ keys(γ1) ∪ wires(st')

                -- keys(γ1) = keys(γ0) ∪ wires(st') ∪ ptrs(st') by postcond of tyEnvAs
                -- and in particular keys(γ1) ∪ wires(st') ⊆ keys(γ1).
                -- therefore j ∈ keys(γ1), and because γ2 ≥ γ1 and γ2[j] = TBool,
                -- also γ1[j] = TBool                                        (B)

                ?? lookupLemma j γ2      -- lookup j γ2 == Just (γ2[j])
                ?? tyEnvEIncr e' γ1 γ2 j -- γ1[j] == γ2[j] since γ2 ≥ γ1
                ?? lookupLemma j γ1      -- lookup j γ1 == Just (γ1[j])

                -- (A)+(B) together mean that h_bool1 is applicable
                ?? h_bool1 j



{-@ booleanProofAs' :: m:Nat
                    -> σ:WireValuation p m
                    -> st:[LAss p (Btwn 0 m)]
                    -> γ:TyEnv' (Btwn 0 m)
                    -> γ':{TyEnv' (Btwn 0 m) | Just γ' = tyEnvAs st γ}
                    -> j:{Btwn 0 m | S.member j (wiresAs st)
                                && M.lookup j γ' = Just TBool}
                    -> { coherentAs m σ st => boolean (M.lookup' j σ) } @-}
booleanProofAs' :: (Fractional p, Eq p)
                => Int -> WireValuation p -> [LAss p Int]
                -> TyEnv' Int -> TyEnv' Int -> Int
                -> Proof
booleanProofAs' m σ st γ γ' j = case st of
  [] -> trivial
  a:as -> if S.member j (wiresAs as)
          then booleanProofAs' m σ as γ1 γ2 j -- if j ∈ wires(as)
          else lookupLemma j γ1 -- otherwise, j ∈ wires(a)
            ?? γ2_ge_γ1 j
            ?? lookupLemma j γ2
            ?? booleanProofA  m σ a  γ  γ1 j
    where γ1 = case tyEnvA  a  γ  of Just g -> g
          γ2 = case tyEnvAs as γ1 of Just g -> g

          {-@ γ2_ge_γ1 :: MapGE γ2 γ1 @-}
          γ2_ge_γ1 :: Int -> Proof
          γ2_ge_γ1 = tyEnvAsIncr as γ1 γ2




-- workarounds to fix "crash: unknown constant" --------------------------------

{-@ reflect foo @-}
foo :: UnOp Int -> Int
foo (ADDC x) = x
foo _        = 0

{-@ reflect barOp @-}
barOp :: BinOp Int -> Int
barOp ADD = 0
barOp _   = 1
