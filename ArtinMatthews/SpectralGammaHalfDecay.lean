module

public import ArtinMatthews.SpectralGammaReflectionStrip
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Complex
open scoped ComplexConjugate
noncomputable section

theorem spectralGamma_vertical_norm_even (a t : ℝ) :
    ‖Complex.Gamma ((a : ℂ) + ((-t : ℝ) : ℂ) * I)‖ =
      ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ := by
  have heq : (a : ℂ) + ((-t : ℝ) : ℂ) * I = conj ((a : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [heq, Complex.Gamma_conj, norm_conj]

theorem spectralGamma_half_norm_sq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hconj : 1 - z = conj z := by
    apply Complex.ext <;> norm_num [z, Complex.mul_re, Complex.mul_im]
  have hsin : Complex.sin ((Real.pi : ℂ) * z) = (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * I + (Real.pi : ℂ) / 2 by
      dsimp [z]; push_cast; ring]
    rw [Complex.sin_add_pi_div_two, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  have heq := congrArg norm (Complex.Gamma_mul_Gamma_one_sub z)
  rw [hconj, Complex.Gamma_conj, norm_mul, norm_conj, norm_div, hsin,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos _).le] at heq
  simpa only [pow_two] using heq

theorem spectralGamma_five_half_norm_sq (t : ℝ) :
    ‖Complex.Gamma ((5 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ((t ^ 2 + 1 / 4) * (t ^ 2 + 9 / 4)) * Real.pi / Real.cosh (Real.pi * t) := by
  let z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at hre
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at hre
  have harg : (5 / 2 : ℂ) + (t : ℂ) * I = (z + 1) + 1 := by dsimp [z]; ring
  have hn0 : ‖z‖ ^ 2 = t ^ 2 + 1 / 4 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [z, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two, add_comm]
  have hn1 : ‖z + 1‖ ^ 2 = t ^ 2 + 9 / 4 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [z, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two, add_comm]
  calc
    _ = ‖z + 1‖ ^ 2 * ‖z‖ ^ 2 * ‖Complex.Gamma z‖ ^ 2 := by
      rw [harg, Complex.Gamma_add_one _ hz1, Complex.Gamma_add_one _ hz]
      simp only [norm_mul, mul_pow]
      ring
    _ = _ := by
      rw [hn1, hn0, spectralGamma_half_norm_sq t]
      ring

end
end ArtinMatthews
