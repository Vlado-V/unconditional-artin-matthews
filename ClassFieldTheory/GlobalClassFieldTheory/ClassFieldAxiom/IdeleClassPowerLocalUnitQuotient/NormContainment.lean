module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdelePowerLocalUnitNormContainment
public import Mathlib.Data.Nat.Choose.Multinomial
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
# Norm containment for idele power-local-unit subgroups

This file proves that the concrete local-condition subgroup lies in the global
idele norm range, and descends that inclusion to idele classes.
-/

open scoped NumberField Classical NNReal ValuativeRel TensorProduct
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations
open KummerTheory
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The idele norm inclusion `h(S,T) ⊆ N_{L/K} I_L`. -/
theorem idelePowerLocalUnitSubgroup_le_relativeIdeleNorm_range
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal)
    (hT :
      ∀ v, v ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (hAway :
      ∀ v, v ∉ S ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v) :
    idelePowerLocalUnitSubgroup (K := K) n S T ≤
      (RelativeIdeleGroup.norm K L).range := by
  intro a ha
  rw [_root_.mem_relativeIdeleNorm_range_iff_localTensorNorms]
  constructor
  · intro w
    apply
      _root_.infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
        (K := K) (L := L) w
    apply
      nthPowerSubgroup_le_infinitePositiveSubgroup
        (K := K) n w
    · exact harch.imp_right (fun h => h w)
    · exact
        ((mem_idelePowerLocalUnitSubgroup_iff
          (K := K) n S T a).mp ha).1 w
  · intro v
    rw [
      _root_.finitePlaceLocalTensorNorm_range_eq_chosenLocalNormSubgroup]
    have hall :=
      idelePowerLocalUnitSubgroup_le_allFinitePlaceLocalNormCondition
        (K := K) (L := L) n r eG S T hT hAway ha
    exact Subgroup.mem_iInf.mp hall v

/-- The induced norm inclusion on idele class groups:
`N_{L/K} C_L ⊇ C_K(S,T)`. -/
theorem ideleClassPowerLocalUnitSubgroup_le_ideleClassNorm_range
    (n : ℕ+) (r : ℕ)
    (eG :
      (L ≃ₐ[K] L) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (harch :
      Even (n : ℕ) ∨
        ∀ w : InfinitePlace K, ¬ w.IsReal)
    (hT :
      ∀ v, v ∈ T →
        _root_.FinitePlaceSplitsCompletely
          (K := K) (L := L) v)
    (hAway :
      ∀ v, v ∉ S ∪ T →
        _root_.ChosenFinitePlaceIsUnramified
          (K := K) (L := L) v) :
    ideleClassPowerLocalUnitSubgroup (K := K) n S T ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range := by
  rintro c ⟨a, ha, rfl⟩
  obtain ⟨b, hb⟩ :=
    idelePowerLocalUnitSubgroup_le_relativeIdeleNorm_range
      (K := K) (L := L) n r eG S T harch hT hAway ha
  refine
    ⟨QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) b, ?_⟩
  rw [RelativeIdeleGroup.Cohomology.ideleClassNorm_mk, hb]


end GlobalClassFieldTheory.ClassFieldAxiom
