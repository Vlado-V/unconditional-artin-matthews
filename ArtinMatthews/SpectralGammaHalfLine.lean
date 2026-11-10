module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta


set_option backward.privateInPublic true
@[expose] public section

/-! A reciprocal-Gamma bound on the central vertical line from the actual
Gamma reflection formula; no asymptotic Gamma estimate is assumed. -/
namespace ArtinMatthews

open Complex
open scoped ComplexConjugate

lemma spectral_norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have H := norm_sub_le (Complex.exp (-z*Complex.I)) (Complex.exp (z*Complex.I))
  have hp : ‖Complex.exp (-z*Complex.I)‖ = Real.exp z.im := by
    simp [Complex.norm_exp,Complex.mul_re]
  have hm : ‖Complex.exp (z*Complex.I)‖ = Real.exp (-z.im) := by
    simp [Complex.norm_exp,Complex.mul_re]
  rw [hp,hm] at H
  have h₁ := Real.exp_le_exp.mpr (le_abs_self z.im)
  have h₂ := Real.exp_le_exp.mpr (neg_le_abs z.im)
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one]
  norm_num only [norm_ofNat]
  linarith

theorem spectral_inv_gamma_half_line (t : ℝ) :
    ‖(Complex.Gamma (⟨1/2,2*t⟩ : ℂ))⁻¹‖ ≤ Real.exp (Real.pi*|t|) := by
  let z : ℂ := ⟨1/2,2*t⟩
  have hc : 1-z = conj z := by
    apply Complex.ext <;> norm_num [z]
  have hg : 0 < ‖Complex.Gamma z‖ := norm_pos_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (by dsimp [z]; norm_num))
  have H := congrArg norm (Complex.Gamma_mul_Gamma_one_sub z)
  rw [hc,Complex.Gamma_conj,norm_mul,norm_conj,norm_div] at H
  have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by simp
  rw [hp] at H
  have hn : ‖Complex.sin ((Real.pi : ℂ)*z)‖ ≠ 0 := by
    intro h
    rw [h,div_zero] at H
    nlinarith
  have HE : ‖Complex.Gamma z‖*‖Complex.Gamma z‖ *
      ‖Complex.sin ((Real.pi : ℂ)*z)‖ = Real.pi := (eq_div_iff hn).mp H
  have him : |((Real.pi : ℂ)*z).im| = 2*Real.pi*|t| := by
    simp [z,abs_mul]
    ring
  have hsin : ‖Complex.sin ((Real.pi : ℂ)*z)‖ ≤
      (Real.exp (Real.pi*|t|))^2 := by
    apply (spectral_norm_sin_le_exp_abs_im _).trans_eq
    rw [him]
    calc
      _ = Real.exp (Real.pi*|t| + Real.pi*|t|) := by congr 1; ring
      _ = _ := by rw [Real.exp_add,pow_two]
  have hm := mul_le_mul_of_nonneg_left hsin
    (mul_nonneg (norm_nonneg (Complex.Gamma z)) (norm_nonneg (Complex.Gamma z)))
  rw [HE] at hm
  have hsq : (1 : ℝ)^2 ≤ (‖Complex.Gamma z‖*Real.exp (Real.pi*|t|))^2 := by
    nlinarith [Real.one_le_pi_div_two]
  have hprod : 1 ≤ ‖Complex.Gamma z‖*Real.exp (Real.pi*|t|) :=
    le_of_sq_le_sq hsq (by positivity)
  change ‖(Complex.Gamma z)⁻¹‖ ≤ _
  rw [norm_inv,← one_div]
  apply (div_le_iff₀ hg).2
  simpa only [mul_comm] using hprod

end ArtinMatthews
