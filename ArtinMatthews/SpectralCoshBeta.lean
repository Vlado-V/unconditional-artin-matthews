module

public import ArtinMatthews.SpectralBetaLogistic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact beta evaluation of the cosh Laplace profile. This will supply
the Mellin transform of exp(-x)K_nu(x) from its actual cosh integral. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectral_sigmoid_cosh_product (u : ℝ) :
    Real.sigmoid u*(1-Real.sigmoid u) = (2*(1+Real.cosh u))⁻¹ := by
  rw [Real.sigmoid_def,Real.cosh_eq,Real.exp_neg]
  field_simp [(Real.exp_pos u).ne']
  ring

def spectralCoshBetaProfile (s ν : ℂ) (u : ℝ) : ℂ :=
  ((1+Real.cosh u : ℝ) : ℂ)^(-s)*Complex.exp (ν*(u : ℂ))

theorem spectralCoshBetaProfile_eq (s ν : ℂ) (u : ℝ) :
    spectralCoshBetaProfile s ν u = (2 : ℂ)^s*spectralBetaLogProfile (s+ν) (s-ν) u := by
  have hs : 0 < Real.sigmoid u := Real.sigmoid_pos u
  have ht : 0 < 1-Real.sigmoid u := sub_pos.mpr (Real.sigmoid_lt_one u)
  have hc : 0 < 1+Real.cosh u := by linarith [Real.one_le_cosh u]
  rw [spectralBetaLogProfile_shift]
  unfold spectralBetaLogProfile spectralCoshBetaProfile
  rw [← Complex.mul_cpow_ofReal_nonneg hs.le ht.le,← Complex.ofReal_mul,spectral_sigmoid_cosh_product,
    Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg (by positivity : (0 : ℝ) ≤ 2*(1+Real.cosh u))]
  rw [Complex.ofReal_mul,Complex.ofReal_ofNat]
  have hm : ((2 : ℂ)*((1+Real.cosh u : ℝ) : ℂ))^s =
      (2 : ℂ)^s*((1+Real.cosh u : ℝ) : ℂ)^s := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := 1+Real.cosh u) (by norm_num) hc.le s
  rw [hm]
  have h2 : (2 : ℂ)^s ≠ 0 := by rw [Complex.cpow_def_of_ne_zero (by norm_num)]; exact Complex.exp_ne_zero _
  have hC : (((1+Real.cosh u : ℝ) : ℂ)^s)⁻¹ = ((1+Real.cosh u : ℝ) : ℂ)^(-s) :=
    (Complex.cpow_neg _ _).symm
  rw [mul_inv,hC]
  field_simp

theorem spectralCoshBetaProfile_integrable (s ν : ℂ) (hs : |ν.re| < s.re) :
    Integrable (spectralCoshBetaProfile s ν) := by
  have ha : 0 < (s+ν).re := by
    simp only [Complex.add_re]
    linarith [neg_le_abs ν.re]
  have hb : 0 < (s-ν).re := by
    simp only [Complex.sub_re]
    linarith [le_abs_self ν.re]
  apply ((spectralBetaLogProfile_integrable (s+ν) (s-ν) ha hb).const_mul ((2 : ℂ)^s)).congr
  filter_upwards with u
  exact (spectralCoshBetaProfile_eq s ν u).symm

theorem spectralCoshBetaProfile_integral (s ν : ℂ) :
    (∫ u : ℝ, spectralCoshBetaProfile s ν u) = (2 : ℂ)^s*Complex.betaIntegral (s+ν) (s-ν) := by
  simp_rw [spectralCoshBetaProfile_eq]
  rw [integral_const_mul,spectralBetaLogProfile_integral]

end ArtinMatthews
