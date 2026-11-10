module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.Local
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.H0
public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Family.HMinusOne
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

set_option autoImplicit false

/-!
# Finite unrestricted local-block families

This leaf assembles the local Herbrand calculations over the finite family of
unrestricted places.
-/

open scoped NumberField BigOperators ValuativeRel Classical NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] in
/-- Degree-zero cohomology of the finite family of unrestricted local
blocks is finite. -/
theorem relativeUnrestrictedLocalBlockFamilyHerbrandH0Finite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : ∀ i, MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      fun i =>
        decompositionGroupLocalUnitsAction
          (d i).base (d i).base_isNontrivial
          (d i).extension
    letI : ∀ i, MulDistribMulAction
        (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
      fun i =>
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
    letI : MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i =>
          LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension)
    Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (LocalBlockFamily d)) := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let localAction :=
    localBlockFamilyLocalAction d
  let blockAction :=
    localBlockFamilyBlockAction d
  let familyAction :=
    localBlockFamilyCohomologyAction d
  let decompositionFintype :=
    localBlockFamilyDecompositionFintype d
  let localFinite : ∀ i, Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ) :=
    fun i =>
      relativeUnrestrictedLocalHerbrandH0Finite
        S i σ hgen
  exact
    Finite.of_equiv
      (∀ i,
        HerbrandH0
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ)
      (localBlockFamilyHerbrandH0Equiv
        d σ hgen).symm.toEquiv

omit [NumberField L] in
/-- Degree-minus-one cohomology of the finite family of unrestricted
local blocks is finite. -/
theorem relativeUnrestrictedLocalBlockFamilyHerbrandHMinusOneFinite
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    let d :=
      relativeUnrestrictedSPlaceDatum
        (K := K) (L := L) S
    letI : ∀ i, MulDistribMulAction
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ :=
      fun i =>
        decompositionGroupLocalUnitsAction
          (d i).base (d i).base_isNontrivial
          (d i).extension
    letI : ∀ i, MulDistribMulAction
        (L ≃ₐ[K] L)
        (LocalPlaceBlock
          (d i).base (d i).base_isNontrivial
          (d i).extension) :=
      fun i =>
        inducedMulDistribMulAction
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
    letI : MulDistribMulAction (L ≃ₐ[K] L)
        (LocalBlockFamily d) :=
      piMulDistribMulAction (L ≃ₐ[K] L)
        (fun i =>
          LocalPlaceBlock
            (d i).base (d i).base_isNontrivial
            (d i).extension)
    Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (LocalBlockFamily d) σ) := by
  let d :=
    relativeUnrestrictedSPlaceDatum
      (K := K) (L := L) S
  let localAction :=
    localBlockFamilyLocalAction d
  let blockAction :=
    localBlockFamilyBlockAction d
  let familyAction :=
    localBlockFamilyCohomologyAction d
  let decompositionFintype :=
    localBlockFamilyDecompositionFintype d
  let localFinite : ∀ i, Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K (d i).extension.1)
        (LocalizedCompletion
          (d i).base (d i).extension)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          σ hgen)) :=
    fun i =>
      relativeUnrestrictedLocalHerbrandHMinusOneFinite
        S i σ hgen
  exact
    Finite.of_equiv
      (∀ i,
        HerbrandHMinusOne
          (absoluteValueDecompositionGroup K
            (d i).extension.1)
          (LocalizedCompletion
            (d i).base (d i).extension)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K
              (d i).extension.1)
            σ hgen))
      (localBlockFamilyHerbrandHMinusOneEquiv
        d σ hgen).symm.toEquiv
