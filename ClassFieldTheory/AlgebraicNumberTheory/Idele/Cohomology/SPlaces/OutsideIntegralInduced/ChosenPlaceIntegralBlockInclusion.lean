module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlaceAction
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Inclusion
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
# Inclusion of the chosen integral induced block

This file embeds the chosen induced module of local integer units into the
ordinary local multiplicative block and proves injectivity.
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

/-- Inclusion of the chosen integral block into the ordinary chosen
local multiplicative block. -/
noncomputable def chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    ChosenFinitePlaceInducedIntegerUnits
        (K := K) (L := L) w₀ →
      ChosenFinitePlaceLocalPlaceBlock
        (K := K) (L := L) w₀ :=
  by
    letI : MulDistribMulAction
        (absoluteValueDecompositionGroup K
          (chosenFinitePlaceExtension (L := L) w₀).1)
        𝒪[ChosenFinitePlaceLocalizedCompletion
          (K := K) (L := L) w₀]ˣ :=
      chosenFinitePlaceDecompositionGroupIntegerUnitsAction
        (K := K) (L := L) w₀
    change
      InducedModule
          (B := ChosenFinitePlaceLocalizedIntegerUnits
            (K := K) (L := L) w₀)
          (ChosenFinitePlaceDecompositionGroup
            (K := K) (L := L) w₀) →
        ChosenFinitePlaceLocalPlaceBlock
          (K := K) (L := L) w₀
    exact
      (inducedIntegerUnitsToLocalPlaceBlock
          (HeightOneSpectrum.adicAbv K w₀)
          (RayClass.adicAbv_isNontrivial w₀)
          (HeightOneSpectrum.isNonarchimedean_adicAbv K w₀)
          (chosenFinitePlaceExtension (L := L) w₀)).toFun

omit [NumberField L] in
/-- The chosen finite-place integral induced block embeds into its
unrestricted local-place block. -/
theorem chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock_injective
    (w₀ : HeightOneSpectrum (𝓞 K)) :
    Function.Injective
      (chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
        (K := K) (L := L) w₀) := by
  let vK := HeightOneSpectrum.adicAbv K w₀
  let u := chosenFinitePlaceExtension (L := L) w₀
  let hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial w₀
  let hvKna : IsNonarchimedean (vK : K → ℝ) :=
    HeightOneSpectrum.isNonarchimedean_adicAbv K w₀
  unfold chosenFinitePlaceIntegralInducedBlockToLocalPlaceBlock
  exact inducedIntegerUnitsToLocalPlaceBlock_injective
    vK hvK hvKna u
end ChosenFinitePlace
