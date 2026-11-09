module

public import ArtinMatthews.SpectralKLUnitary
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper


set_option backward.privateInPublic true
@[expose] public section

/-! Literal frequency dilation preserves dx/x; no hidden frequency or
cusp-width scalar is absorbed into the KL normalization. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralKLPhysical_dilation_integral (F : ℝ → ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ x in Ioi (0 : ℝ), F (x/q)/(x : ℂ)) = ∫ y in Ioi (0 : ℝ), F y/(y : ℂ) := by
  have h := integral_comp_mul_left_Ioi' (fun x : ℝ => F (x/q)/(x : ℂ)) 0 hq
  simp only [mul_zero] at h
  calc
    _ = q • ∫ y in Ioi (0 : ℝ), F (q*y/q)/((q*y : ℝ) : ℂ) := h.symm
    _ = _ := by
      rw [← integral_smul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only
      rw [Complex.real_smul,mul_div_cancel_left₀ y hq.ne',Complex.ofReal_mul]
      have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
      field_simp

theorem spectralKLPhysical_dilation_real_integral (F : ℝ → ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ x in Ioi (0 : ℝ), F (x/q)/x) = ∫ y in Ioi (0 : ℝ), F y/y := by
  have h := spectralKLPhysical_dilation_integral (fun x => (F x : ℂ)) hq
  have hc : (∫ x in Ioi (0 : ℝ), (F (x/q) : ℂ)/(x : ℂ)) =
      ((∫ x in Ioi (0 : ℝ), F (x/q)/x : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_div]
    exact integral_complex_ofReal
  have hc' : (∫ y in Ioi (0 : ℝ), (F y : ℂ)/(y : ℂ)) =
      ((∫ y in Ioi (0 : ℝ), F y/y : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_div]
    exact integral_complex_ofReal
  rw [hc,hc'] at h
  exact Complex.ofReal_injective h

end ArtinMatthews
