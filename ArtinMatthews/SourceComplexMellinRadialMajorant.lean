module

public import ArtinMatthews.SourceComplexTraceFourier
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set
open scoped SchwartzMap
noncomputable section

def sourceComplexMellinRadialPower (σ : ℝ) : ℕ := Nat.ceil (2 * σ) + 3

def sourceComplexMellinRadialMajorant (σ : ℝ) (z : ℂ) : ℝ :=
  (1 + ‖z‖) ^ (-(sourceComplexMellinRadialPower σ : ℝ)) * ‖z‖ ^ (2 * σ - 2)

theorem sourceComplexMellinRadialMajorant_nonneg (σ : ℝ) (z : ℂ) :
    0 ≤ sourceComplexMellinRadialMajorant σ z := by
  unfold sourceComplexMellinRadialMajorant
  positivity

theorem sourceComplexMellinRadialMajorant_near (σ : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖sourceComplexMellinRadialMajorant σ z‖ ≤ ‖z‖ ^ (-(max 0 (2 - 2 * σ))) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sourceComplexMellinRadialMajorant_nonneg σ z)]
  unfold sourceComplexMellinRadialMajorant
  have hf : (1 + ‖z‖) ^ (-(sourceComplexMellinRadialPower σ : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (norm_nonneg _)) (neg_nonpos.mpr (Nat.cast_nonneg _))
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (norm_nonneg _) _) hf).trans
  by_cases hzero : z = 0
  · subst z
    by_cases h : 2 * σ - 2 = 0
    · have hσ : σ = 1 := by linarith
      norm_num [hσ]
    · simpa only [norm_zero, Real.zero_rpow h] using
        Real.rpow_nonneg (by norm_num : 0 ≤ (0 : ℝ)) (-(max 0 (2 - 2 * σ)))
  · exact Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hzero) hz (by
      linarith [le_max_right (0 : ℝ) (2 - 2 * σ)])

theorem sourceComplexMellinRadialMajorant_far (σ : ℝ) (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖sourceComplexMellinRadialMajorant σ z‖ ≤ (1 + ‖z‖) ^ (-(3 : ℝ)) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sourceComplexMellinRadialMajorant_nonneg σ z)]
  unfold sourceComplexMellinRadialMajorant
  have he : 2 * σ - 2 ≤ (Nat.ceil (2 * σ) : ℝ) := by linarith [Nat.le_ceil (2 * σ)]
  have hn : ‖z‖ ^ (2 * σ - 2) ≤ (1 + ‖z‖) ^ (Nat.ceil (2 * σ) : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hz he).trans
      (Real.rpow_le_rpow (norm_nonneg _) (by linarith) (Nat.cast_nonneg _))
  calc
    _ ≤ (1 + ‖z‖) ^ (-(sourceComplexMellinRadialPower σ : ℝ)) *
        (1 + ‖z‖) ^ (Nat.ceil (2 * σ) : ℝ) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (by positivity : 0 < 1 + ‖z‖)]
      congr 1
      unfold sourceComplexMellinRadialPower
      push_cast
      ring

theorem sourceComplexMellinRadialMajorant_integrable (σ : ℝ) (hσ : 0 < σ) :
    Integrable (sourceComplexMellinRadialMajorant σ) sourceComplexTraceMeasure := by
  have hm : AEStronglyMeasurable (sourceComplexMellinRadialMajorant σ) := by
    apply Measurable.aestronglyMeasurable
    unfold sourceComplexMellinRadialMajorant
    fun_prop
  have ha : max 0 (2 - 2 * σ) < 2 := max_lt_iff.mpr ⟨by norm_num, by linarith⟩
  have hn : IntegrableOn (sourceComplexMellinRadialMajorant σ) (Metric.ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp [Complex.finrank_real_complex])
      (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using ha)
      (C := 1) (α := max 0 (2 - 2 * σ)) _ hm
    filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet] with z hz
    have hr : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    simpa only [one_mul] using sourceComplexMellinRadialMajorant_near σ z hr.le
  have hf : IntegrableOn (sourceComplexMellinRadialMajorant σ) (Metric.ball (0 : ℂ) 1)ᶜ := by
    have hi : Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-(3 : ℝ))) :=
      integrable_one_add_norm (by norm_num [Complex.finrank_real_complex])
    apply hi.integrableOn.mono' hm.restrict
    filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet.compl] with z hz
    have hr : 1 ≤ ‖z‖ := by simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
    exact sourceComplexMellinRadialMajorant_far σ z hr
  have h : Integrable (sourceComplexMellinRadialMajorant σ) := by
    simpa only [union_compl_self, integrableOn_univ] using hn.union hf
  exact h.smul_measure (by norm_num : (2 : ENNReal) ≠ ⊤)

end
end ArtinMatthews.VaryingKummerAnalytic
