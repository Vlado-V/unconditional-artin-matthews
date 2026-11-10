module

public import ArtinMatthews.SourceSheetWeightedPointwise
public import ArtinMatthews.SourceCircleHaar
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set Filter
open scoped SchwartzMap ENNReal Topology
noncomputable section

variable {Y : Type*} [MeasurableSpace Y]

def sourceSheetProfileIntegrand (N : Y → ℝ) (g : 𝓢(ℂ, ℂ)) (G : Y → ℂ)
    (t : ℝ) (p : Circle × Y) : ℂ :=
  g (sourceSheetComplexCoordinate N t p.1 p.2) * G p.2

def sourceSheetLogProfile (ν : Measure Y) (N : Y → ℝ) (g : 𝓢(ℂ, ℂ)) (G : Y → ℂ) (t : ℝ) : ℂ :=
  ∫ p : Circle × Y, sourceSheetProfileIntegrand N g G t p ∂sourceCircleHaar.prod ν

instance sourceCircleHaar_finite : IsFiniteMeasure sourceCircleHaar :=
  ⟨by rw [sourceCircleHaar_univ]; exact ENNReal.ofReal_lt_top⟩

theorem sourceSheetProfileIntegrand_measurable (N : Y → ℝ) (hN : Measurable N)
    (g : 𝓢(ℂ, ℂ)) (G : Y → ℂ) (hG : Measurable G) (t : ℝ) :
    Measurable (sourceSheetProfileIntegrand N g G t) := by
  have hr : Measurable (fun p : Circle × Y => Real.exp ((t - Real.log (N p.2)) / 2)) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.sub (Real.measurable_log.comp (hN.comp measurable_snd))).div_const 2)
  exact (g.continuous.measurable.comp
    ((Complex.continuous_ofReal.measurable.comp hr).mul
      (Circle.measurable_coe.comp measurable_fst))).mul (hG.comp measurable_snd)

omit [MeasurableSpace Y] in
theorem sourceSheetProfileIntegrand_norm_le (N : Y → ℝ) (hN : ∀ y, 0 < N y)
    (g : 𝓢(ℂ, ℂ)) (G : Y → ℂ) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (p : Circle × Y),
      ‖sourceSheetProfileIntegrand N g G t p‖ ≤
        (C * Real.exp (-σ * t)) * (‖G p.2‖ * (N p.2) ^ σ) := by
  obtain ⟨C,hC,hb⟩ := sourceSheetComplexCoordinate_weighted_sup N hN g σ hσ
  refine ⟨C,hC,fun t p => ?_⟩
  rw [sourceSheetProfileIntegrand, norm_mul]
  calc
    _ ≤ ((C * Real.exp (-σ * t)) * (N p.2) ^ σ) * ‖G p.2‖ :=
      mul_le_mul_of_nonneg_right (hb t p.1 p.2) (norm_nonneg _)
    _ = _ := by ac_rfl

theorem sourceSheetLogProfile_integrable_and_bound (ν : Measure Y) [SFinite ν]
    (N : Y → ℝ) (hN : ∀ y, 0 < N y) (hNm : Measurable N)
    (g : 𝓢(ℂ, ℂ)) (G : Y → ℂ) (hG : Measurable G) (σ : ℝ) (hσ : 0 < σ)
    (hInt : Integrable (fun y => ‖G y‖ * (N y) ^ σ) ν) :
    (∀ t, Integrable (sourceSheetProfileIntegrand N g G t) (sourceCircleHaar.prod ν)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖sourceSheetLogProfile ν N g G t‖ ≤ C * Real.exp (-σ * t) := by
  obtain ⟨C,hC,hb⟩ := sourceSheetProfileIntegrand_norm_le N hN g G σ hσ
  let W : Circle × Y → ℝ := fun p => ‖G p.2‖ * (N p.2) ^ σ
  have hW : Integrable W (sourceCircleHaar.prod ν) := hInt.comp_snd sourceCircleHaar
  have hW0 (p : Circle × Y) : 0 ≤ W p :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hN p.2).le _)
  have hI (t : ℝ) : Integrable (sourceSheetProfileIntegrand N g G t) (sourceCircleHaar.prod ν) :=
    (hW.const_mul (C * Real.exp (-σ * t))).mono'
      (sourceSheetProfileIntegrand_measurable N hNm g G hG t).aestronglyMeasurable
      (Eventually.of_forall (hb t))
  refine ⟨hI, ⟨C * (∫ p, W p ∂sourceCircleHaar.prod ν),
    mul_nonneg hC (integral_nonneg hW0), fun t => ?_⟩⟩
  unfold sourceSheetLogProfile
  calc
    _ ≤ ∫ p, ‖sourceSheetProfileIntegrand N g G t p‖ ∂sourceCircleHaar.prod ν :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ p, (C * Real.exp (-σ * t)) * W p ∂sourceCircleHaar.prod ν :=
      integral_mono (hI t).norm (hW.const_mul _) (hb t)
    _ = _ := by rw [integral_const_mul]; ac_rfl

end
end ArtinMatthews.SourcePhysical
