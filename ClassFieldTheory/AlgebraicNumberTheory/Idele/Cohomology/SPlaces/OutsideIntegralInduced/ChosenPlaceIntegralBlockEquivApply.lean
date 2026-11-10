module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockEquiv
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceIntegralBlockInclusion
public import ClassFieldTheory.AlgebraicNumberTheory.Adele.FinitePlaceTensorBlock
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
# Compatibility of the chosen integral equivalence and inclusion

This file compares the integral-block inclusion with the finite-place tensor
equivalence on underlying field units.
-/

open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section ChosenFinitePlace

omit [NumberField L] in
/-- The integral-block inclusion is compatible with the pre-existing
local-block equivalence on underlying field units. -/
theorem
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_equiv_apply
    (w₀ : HeightOneSpectrum (𝓞 K))
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w₀) :
    chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
        (K := K) (L := L) w₀
        (relativeLocalTensorDecompositionIntegralUnitSubgroupEquivInducedIntegerUnits
          (K := K) (L := L) w₀ x) =
      finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (x : (w₀.adicCompletion K ⊗[K] L)ˣ) := by
  let vK := HeightOneSpectrum.adicAbv K w₀
  let u := chosenFinitePlaceExtension (L := L) w₀
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial w₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K w₀
  let := decompositionGroupLocalUnitsAction vK hvK u
  apply
    (inducedRightCosetCoordinates
      (absoluteValueDecompositionGroup K u.1)).injective
  funext q
  apply Units.ext
  rfl
end ChosenFinitePlace
