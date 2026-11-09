module

public import ArtinMatthews.SpectralBesselOrderFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The spectral-edge majorant of the literal Gamma/sinh denominator.
It is at most C/t near zero and uniformly bounded at large order. -/

noncomputable section

namespace ArtinMatthews

theorem spectralBesselOrderFactor_small {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    1/spectralBesselOrderDenominator t ≤ Real.sqrt (Real.cosh Real.pi)/(Real.pi*t) := by
  have hd := spectralBesselOrderDenominator_pos ht
  have hpt : 0 < Real.pi*t := mul_pos Real.pi_pos ht
  have hc : 0 < Real.cosh (Real.pi*t) := by linarith [Real.one_le_cosh (Real.pi*t)]
  have hcpi : 0 ≤ Real.cosh Real.pi := by linarith [Real.one_le_cosh Real.pi]
  have hcosh : Real.cosh (Real.pi*t) ≤ Real.cosh Real.pi := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_pos hpt,abs_of_pos Real.pi_pos]
    nlinarith
  have hsinh : Real.pi*t ≤ Real.sinh (Real.pi*t) := Real.self_le_sinh_iff.mpr hpt.le
  have hprod : (spectralBesselOrderDenominator t)^2*Real.cosh (Real.pi*t) =
      Real.pi*t*Real.sinh (Real.pi*t) := by
    rw [spectralBesselOrderDenominator_sq ht]
    field_simp
  have hsq : (Real.pi*t)^2 ≤ (Real.sqrt (Real.cosh Real.pi)*spectralBesselOrderDenominator t)^2 := by
    simp only [mul_pow,Real.sq_sqrt hcpi]
    calc
      _ ≤ Real.pi*t*Real.sinh (Real.pi*t) := by nlinarith [mul_le_mul_of_nonneg_left hsinh hpt.le]
      _ = (spectralBesselOrderDenominator t)^2*Real.cosh (Real.pi*t) := hprod.symm
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hcosh (sq_nonneg (spectralBesselOrderDenominator t))]
  have hlin : Real.pi*t ≤ Real.sqrt (Real.cosh Real.pi)*spectralBesselOrderDenominator t :=
    (sq_le_sq₀ hpt.le (mul_nonneg (Real.sqrt_nonneg _) hd.le)).mp hsq
  exact (div_le_div_iff₀ hd hpt).mpr (by simpa only [one_mul] using hlin)

theorem spectralBesselOrderFactor_bound {t : ℝ} (ht : 0 < t) :
    1/spectralBesselOrderDenominator t ≤ 1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t := by
  by_cases ht1 : t ≤ 1
  · have h := spectralBesselOrderFactor_small ht ht1
    have he : Real.sqrt (Real.cosh Real.pi)/(Real.pi*t) = (Real.sqrt (Real.cosh Real.pi)/Real.pi)/t := by ring
    rw [he] at h
    linarith
  · have h := spectralBesselOrderFactor_large (le_of_lt (lt_of_not_ge ht1))
    have hp : 0 ≤ (Real.sqrt (Real.cosh Real.pi)/Real.pi)/t := by positivity
    linarith

end ArtinMatthews
