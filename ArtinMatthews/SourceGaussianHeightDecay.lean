module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Gaussian height convolution in section 06. Integrating in
the other Mellin height preserves arbitrary polynomial decay in the remaining
height, with a constant independent of that height. -/

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped Topology
noncomputable section

theorem source_gaussian_polynomial_integrable (n : ℕ) :
    Integrable (fun x : ℝ => (1 + |x|) ^ n * Real.exp (-(x ^ 2))) := by
  have h0 : Integrable (fun x : ℝ => Real.exp (-(x ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hn : Integrable (fun x : ℝ => |x| ^ n * Real.exp (-(x ^ 2))) := by
    have hn0 : (-1 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
    have h := (integrable_rpow_mul_exp_neg_mul_sq (b := 1) (by norm_num)
      (s := (n : ℝ)) hn0).norm
    simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using h
  apply ((h0.add hn).const_mul ((2 : ℝ) ^ (n - 1))).mono'
    (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_right
    (add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg x) n)
    (Real.exp_nonneg (-(x ^ 2)))
  simpa only [one_pow, add_mul, one_mul, mul_assoc, Pi.add_apply] using h

def sourceGaussianPolynomialMoment (n : ℕ) : ℝ :=
  ∫ x : ℝ, (1 + |x|) ^ n * Real.exp (-(x ^ 2))

theorem sourceGaussianPolynomialMoment_nonneg (n : ℕ) :
    0 ≤ sourceGaussianPolynomialMoment n :=
  integral_nonneg (fun _ => by positivity)

theorem source_gaussian_convolution_pointwise (n : ℕ) (T v : ℝ) :
    Real.exp (-((T + v) ^ 2)) / (1 + |v|) ^ n ≤
      ((1 + |T + v|) ^ n * Real.exp (-((T + v) ^ 2))) / (1 + |T|) ^ n := by
  have ht : |T| ≤ |T + v| + |v| := by
    simpa only [add_sub_cancel_right] using abs_sub (T + v) v
  have hb : 1 + |T| ≤ (1 + |T + v|) * (1 + |v|) := by
    nlinarith [abs_nonneg (T + v), abs_nonneg v]
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + |T| by positivity) hb n
  rw [mul_pow] at hp
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-((T + v) ^ 2)))
  nlinarith

theorem source_gaussian_convolution_integrable (n : ℕ) (T : ℝ) :
    Integrable (fun v : ℝ => Real.exp (-((T + v) ^ 2)) / (1 + |v|) ^ n) := by
  have h := ((source_gaussian_polynomial_integrable n).comp_add_left T).div_const
    ((1 + |T|) ^ n)
  have hc : Continuous (fun v : ℝ => Real.exp (-((T + v) ^ 2)) / (1 + |v|) ^ n) :=
    (by fun_prop : Continuous (fun v : ℝ => Real.exp (-((T + v) ^ 2)))).div
      (by fun_prop) (fun v => by positivity)
  apply h.mono' hc.aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_of_nonneg (by positivity)]
  exact source_gaussian_convolution_pointwise n T v

theorem source_gaussian_convolution_decay (n : ℕ) (T : ℝ) :
    (∫ v : ℝ, Real.exp (-((T + v) ^ 2)) / (1 + |v|) ^ n) ≤
      sourceGaussianPolynomialMoment n / (1 + |T|) ^ n := by
  have h := ((source_gaussian_polynomial_integrable n).comp_add_left T).div_const
    ((1 + |T|) ^ n)
  calc
    _ ≤ ∫ v : ℝ, ((1 + |T + v|) ^ n * Real.exp (-((T + v) ^ 2))) /
        (1 + |T|) ^ n := integral_mono
      (source_gaussian_convolution_integrable n T) h
      (source_gaussian_convolution_pointwise n T)
    _ = _ := by
      rw [integral_div, integral_add_left_eq_self
        (fun x : ℝ => (1 + |x|) ^ n * Real.exp (-(x ^ 2))) T]
      rfl

theorem source_gaussian_convolution_uniform_decay (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ,
      (∫ v : ℝ, Real.exp (-((T + v) ^ 2)) / (1 + |v|) ^ n) ≤
        C / (1 + |T|) ^ n := by
  refine ⟨sourceGaussianPolynomialMoment n + 1,
    by linarith [sourceGaussianPolynomialMoment_nonneg n], fun T => ?_⟩
  exact (source_gaussian_convolution_decay n T).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

end
end ArtinMatthews.VaryingKummerAnalytic
