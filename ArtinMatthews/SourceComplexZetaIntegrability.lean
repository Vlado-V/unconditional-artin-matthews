module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Actual absolute convergence for the local complex zeta pairing in
the open critical strip, and its Gaussian Mellin representation. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory Set
open scoped SchwartzMap FourierTransform
noncomputable section

theorem source_complex_schwartz_weighted_integrable (f : 𝓢(ℂ, ℂ))
    (a : ℝ) (ha : 0 ≤ a) (ha2 : a < 2) :
    Integrable (fun z : ℂ => f z * (‖z‖ ^ (-a) : ℝ)) := by
  have hm : AEStronglyMeasurable (fun z : ℂ => f z * (‖z‖ ^ (-a) : ℝ)) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hn : ∀ z : ℂ, ‖f z * (‖z‖ ^ (-a) : ℝ)‖ = ‖f z‖ * ‖z‖ ^ (-a) := by
    intro z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  have hi : IntegrableOn (fun z : ℂ => f z * (‖z‖ ^ (-a) : ℝ)) (Metric.ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp [Complex.finrank_real_complex])
      (by simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using ha2)
      (C := SchwartzMap.seminorm ℝ 0 0 f) (α := a) _ hm
    exact Filter.Eventually.of_forall fun z => by
      rw [hn]
      exact mul_le_mul_of_nonneg_right (f.norm_le_seminorm ℝ z)
        (Real.rpow_nonneg (norm_nonneg z) _)
  have ho : IntegrableOn (fun z : ℂ => f z * (‖z‖ ^ (-a) : ℝ)) (Metric.ball (0 : ℂ) 1)ᶜ := by
    apply f.integrable.norm.integrableOn.mono' hm.restrict
    filter_upwards [self_mem_ae_restrict Metric.isOpen_ball.measurableSet.compl] with z hz
    have hz1 : 1 ≤ ‖z‖ := by simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
    rw [hn]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hz1 (neg_nonpos.mpr ha))
  simpa only [union_compl_self, integrableOn_univ] using hi.union ho

theorem source_complex_schwartz_fourier_weighted_integrable (f : 𝓢(ℂ, ℂ))
    (a : ℝ) (ha : 0 ≤ a) (ha2 : a < 2) :
    Integrable (fun z : ℂ => (𝓕 f : 𝓢(ℂ, ℂ)) z * ((‖z‖ ^ (-a) : ℝ) : ℂ)) :=
  source_complex_schwartz_weighted_integrable (𝓕 f) a ha ha2

theorem source_complex_gaussian_mellin (a : ℝ) (ha : 0 < a)
    (z : ℂ) (hz : z ≠ 0) :
    (∫ t : ℝ in Ioi 0, t ^ (a / 2 - 1) * Real.exp (-(‖z‖ ^ 2 * t))) =
      Real.Gamma (a / 2) * ‖z‖ ^ (-a) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < a / 2) (sq_pos_of_pos hn)]
  have he : (1 / ‖z‖ ^ 2) ^ (a / 2) = ‖z‖ ^ (-a) := by
    rw [one_div, Real.inv_rpow (sq_nonneg _), ← Real.rpow_natCast ‖z‖ 2,
      ← Real.rpow_mul hn.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (a / 2) = a by ring, Real.rpow_neg hn.le]
  rw [he, mul_comm]

end
end ArtinMatthews.VaryingKummerAnalytic
