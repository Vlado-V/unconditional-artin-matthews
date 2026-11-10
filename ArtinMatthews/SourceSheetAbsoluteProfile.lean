module

public import ArtinMatthews.SourceSheetProfile
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

/-! Absolute norm bounds on the split Circle and retained-unit profile. -/

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
open scoped SchwartzMap
noncomputable section

variable {Y : Type*} [MeasurableSpace Y]

theorem sourceSheetLogProfile_integral_norm_le (ν : Measure Y) [SFinite ν]
    (N : Y → ℝ) (hN : ∀ y, 0 < N y) (hNm : Measurable N)
    (g : 𝓢(ℂ, ℂ)) (G : Y → ℂ) (hG : Measurable G) (σ : ℝ) (hσ : 0 < σ)
    (hInt : Integrable (fun y => ‖G y‖ * (N y) ^ σ) ν) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      (∫ p : Circle × Y, ‖sourceSheetProfileIntegrand N g G t p‖ ∂sourceCircleHaar.prod ν) ≤
        C * Real.exp (-σ * t) := by
  obtain ⟨C, hC, hb⟩ := sourceSheetProfileIntegrand_norm_le N hN g G σ hσ
  let W : Circle × Y → ℝ := fun p => ‖G p.2‖ * (N p.2) ^ σ
  have hW : Integrable W (sourceCircleHaar.prod ν) := hInt.comp_snd sourceCircleHaar
  have hW0 (p : Circle × Y) : 0 ≤ W p :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hN p.2).le _)
  have hI := (sourceSheetLogProfile_integrable_and_bound ν N hN hNm g G hG σ hσ hInt).1
  refine ⟨C * (∫ p, W p ∂sourceCircleHaar.prod ν), mul_nonneg hC (integral_nonneg hW0), fun t => ?_⟩
  calc
    _ ≤ ∫ p, (C * Real.exp (-σ * t)) * W p ∂sourceCircleHaar.prod ν :=
      integral_mono (hI t).norm (hW.const_mul _) (hb t)
    _ = _ := by rw [integral_const_mul]; ac_rfl

end
end ArtinMatthews.SourcePhysical
