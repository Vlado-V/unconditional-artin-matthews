module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Convergence of the actual Schläfli integral for every complex order at
a positive real argument. A power bound for the reciprocal exponential
reduces the singular endpoint to an ordinary convergent Gamma integral. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace ArtinMatthews

theorem spectral_exp_neg_div_le_pow (c t : ℝ) (hc : 0 < c) (ht : 0 < t) (n : ℕ) :
    Real.exp (-c / t) ≤ (n.factorial : ℝ) / c ^ n * t ^ n := by
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hu : 0 < c / t := div_pos hc ht
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (c / t) hu.le n)
  have hb : Real.exp (-c / t) ≤ (n.factorial : ℝ) / (c / t) ^ n := by
    apply (le_div_iff₀ (pow_pos hu n)).mpr
    calc
      Real.exp (-c / t) * (c / t) ^ n ≤
          Real.exp (-c / t) * (Real.exp (c / t) * (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
      _ = (n.factorial : ℝ) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp only [neg_div, neg_add_cancel, Real.exp_zero, one_mul]
  calc
    _ ≤ (n.factorial : ℝ) / (c / t) ^ n := hb
    _ = _ := by rw [div_pow]; field_simp

theorem spectral_schlafli_real_majorant (r c t : ℝ) (hc : 0 < c) (ht : 0 < t) (n : ℕ) :
    t ^ (r - 1) * Real.exp (-t - c / t) ≤
      ((n.factorial : ℝ) / c ^ n) * (Real.exp (-t) * t ^ ((r + n) - 1)) := by
  calc
    _ = (t ^ (r - 1) * Real.exp (-t)) * Real.exp (-c / t) := by
      rw [show -t - c / t = -t + (-c / t) by ring, Real.exp_add]
      ring
    _ ≤ (t ^ (r - 1) * Real.exp (-t)) * ((n.factorial : ℝ) / c ^ n * t ^ n) :=
      mul_le_mul_of_nonneg_left (spectral_exp_neg_div_le_pow c t hc ht n)
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
    _ = _ := by
      rw [show (r + (n : ℝ)) - 1 = (r - 1) + n by ring,
        Real.rpow_add ht, Real.rpow_natCast]
      ring

theorem spectral_schlafli_real_integrable (r c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-t - c / t)) (Ioi 0) volume := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-r)
  have hr : 0 < r + (n : ℝ) := by linarith
  have hi := (Real.GammaIntegral_convergent hr).const_mul ((n.factorial : ℝ) / c ^ n)
  apply hi.mono'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_nonneg _))]
    exact spectral_schlafli_real_majorant r c t hc ht n

theorem spectral_schlafli_kernel_norm (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ (ν - 1) * Complex.exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t))‖ =
      t ^ (ν.re - 1) * Real.exp (-t - (x ^ 2 / 4) / t) := by
  have he : -(t : ℂ) - (x : ℂ) ^ 2 / (4 * t) =
      ((-t - (x ^ 2 / 4) / t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, he, Complex.norm_exp]
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]

theorem schlafliIntegral_integrable_all_orders (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (ν - 1) *
      Complex.exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t))) (Ioi 0) volume := by
  have hc : 0 < x ^ 2 / 4 := div_pos (sq_pos_of_pos hx) (by norm_num)
  apply (spectral_schlafli_real_integrable ν.re (x ^ 2 / 4) hc).mono'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (spectral_schlafli_kernel_norm ν x t ht).le

end ArtinMatthews
