module

public import ArtinMatthews.CubicThetaWeightedCuspLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit reduction of every finite rational cusp to the period-dependent Fricke cusp. -/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups Topology
open Complex UpperHalfPlane Filter

/-- The affine upper-half-plane coordinate needed at a finite rational cusp. -/
def eisensteinCuspAux (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0)
    (τ : ℍ) : ℍ :=
  (((γ 1 0 : ℝ) * (γ 1 1 : ℝ) / (3 * (N : ℝ) ^ 2)) +ᵥ
    (⟨(γ 1 0 : ℝ) ^ 2 / (3 * (N : ℝ) ^ 2), by
      have hcR : (γ 1 0 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
      exact div_pos (sq_pos_of_ne_zero hcR) (mul_pos (by norm_num) (sq_pos_of_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N))))⟩ : {x : ℝ // 0 < x}) • τ)

theorem eisensteinCuspAux_coe (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hc : γ 1 0 ≠ 0) (τ : ℍ) :
    (eisensteinCuspAux N γ hc τ : ℂ) =
      (γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) / (3 * (N : ℂ) ^ 2) := by
  simp only [eisensteinCuspAux, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_pos_real_smul,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_intCast, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  ring

theorem eisensteinCuspAux_tendsto (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hc : γ 1 0 ≠ 0) :
    Tendsto (eisensteinCuspAux N γ hc) atImInfty atImInfty := by
  have hcR : (γ 1 0 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hp : 0 < (γ 1 0 : ℝ) ^ 2 / (3 * (N : ℝ) ^ 2) :=
    div_pos (sq_pos_of_ne_zero hcR) (mul_pos (by norm_num) (sq_pos_of_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N))))
  have hi : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  have hh := hi.const_mul_atTop hp
  simpa only [atImInfty, tendsto_comap_iff, Function.comp_def,
    eisensteinCuspAux, UpperHalfPlane.vadd_im, UpperHalfPlane.pos_real_im] using hh

private theorem classical_denominator_ne_zero (γ : SL(2, ℤ)) (hc : γ 1 0 ≠ 0)
    (τ : ℍ) : (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, add_zero, Complex.zero_im] at hi
  exact (mul_ne_zero (Int.cast_ne_zero.mpr hc) τ.im_ne_zero) hi

/-- Möbius action as a rational translation followed by the proved Fricke map. -/
theorem eisensteinCuspAux_decomposition (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hc : γ 1 0 ≠ 0) (τ : ℍ) :
    γ • τ = ((γ 0 0 : ℝ) / (γ 1 0 : ℝ)) +ᵥ
      eisensteinPeriodFricke N (eisensteinCuspAux N γ hc τ) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_vadd]
  change _ = (((γ 0 0 : ℝ) / (γ 1 0 : ℝ) : ℝ) : ℂ) +
    -1 / (3 * (N : ℂ) ^ 2 * (eisensteinCuspAux N γ hc τ : ℂ))
  rw [eisensteinCuspAux_coe]
  have hd : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have hdC : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    exact_mod_cast hd
  have hcC : (γ 1 0 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hc
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hz := classical_denominator_ne_zero γ hc τ
  have hcast (z : ℤ) : ((algebraMap ℤ ℝ z : ℝ) : ℂ) = (z : ℂ) := by simp
  simp only [hcast, Complex.ofReal_div, Complex.ofReal_intCast]
  have hF : (-1 : ℂ) / (3 * (N : ℂ) ^ 2 *
      ((γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) / (3 * (N : ℂ) ^ 2))) =
      (-1 : ℂ) / ((γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) := by
    congr 1
    field_simp
  rw [hF]
  have hz' : (τ : ℂ) * (γ 1 0 : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
    simpa only [mul_comm] using hz
  field_simp [hcC, hz, hz']
  linear_combination -hdC

/-- The weight-one normalizing factors differ by a constant. -/
theorem eisensteinCuspAux_normalization (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hc : γ 1 0 ≠ 0) (τ : ℍ) :
    (eisensteinCuspAux N γ hc τ : ℂ) / ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) =
      (γ 1 0 : ℂ) / (3 * (N : ℂ) ^ 2) := by
  rw [eisensteinCuspAux_coe]
  have hz := classical_denominator_ne_zero γ hc τ
  field_simp

end ArtinMatthews
