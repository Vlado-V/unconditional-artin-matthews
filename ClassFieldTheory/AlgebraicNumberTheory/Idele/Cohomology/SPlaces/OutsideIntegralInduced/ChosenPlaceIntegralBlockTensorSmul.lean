module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.AlgebraicNumberTheory.Adele.FinitePlaceTensorBlock
public import ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralLocalFactor
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
# Equivariance of the integral tensor block

This file proves equivariance of the finite-place tensor-unit block under the
restricted global Galois action.
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
/-- The local-place block equivalence intertwines the restricted integral
tensor action with the global Galois action. -/
theorem
    finitePlaceTensorUnitsEquivLocalPlaceBlock_restricted_smul
    (w₀ : HeightOneSpectrum (𝓞 K))
    (τ : L ≃ₐ[K] L)
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w₀) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w₀
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (((τ • x :
            relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w₀)) :
          (w₀.adicCompletion K ⊗[K] L)ˣ) =
      τ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀)
          (x : (w₀.adicCompletion K ⊗[K] L)ˣ) := by
  let :=
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
      (K := K) (L := L) w₀
  let tensorUnitsAction :=
    scalarTensorUnitsAction
      (K := K) (L := L) (A := w₀.adicCompletion K)
  calc
    finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (((τ • x :
            relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w₀)) :
          (w₀.adicCompletion K ⊗[K] L)ˣ) =
      finitePlaceTensorUnitsEquivLocalPlaceBlock
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀)
        (τ • (x : (w₀.adicCompletion K ⊗[K] L)ˣ)) :=
      congrArg
        (finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀))
        (relativeLocalTensorDecompositionIntegralUnitSubgroupAction_coe
          (K := K) (L := L) w₀ τ x)
    _ = τ •
        finitePlaceTensorUnitsEquivLocalPlaceBlock
          (K := K) (L := L) w₀
          (chosenFinitePlaceExtension (L := L) w₀)
          (x : (w₀.adicCompletion K ⊗[K] L)ˣ) :=
      finitePlaceTensorUnitsEquivLocalPlaceBlock_smul
        (K := K) (L := L) w₀
        (chosenFinitePlaceExtension (L := L) w₀) τ
        (x : (w₀.adicCompletion K ⊗[K] L)ˣ)

end ChosenFinitePlace
