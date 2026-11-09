module

public import ArtinMatthews.SpectralBesselCoshEvaluation
public import OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage


set_option backward.privateInPublic true
@[expose] public section

/-! The actual two-variable Mellin/Schläfli mixture for arbitrary complex
order.  Both Gamma half-planes are explicit. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralSchlafliMellinMixture (ν s : ℂ) (t x : ℝ) : ℂ :=
  (t : ℂ)^(ν-1)*Complex.exp (-(t : ℂ)) *
    ((x : ℂ)^((s-ν)-1)*Complex.exp (-((1/(4*t) : ℝ) : ℂ)*(x : ℂ)^2))

theorem spectralSchlafliMellinMixture_slice_integrable (ν s : ℂ)
    (hs : ν.re < s.re) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (spectralSchlafliMellinMixture ν s t) (Ioi 0) := by
  exact (complex_gaussian_power_integrable (s-ν) (1/(4*t))
    (by simpa only [Complex.sub_re] using sub_pos.mpr hs) (by positivity)).const_mul _

theorem spectralSchlafliMellinMixture_integral_x (ν s : ℂ)
    (hs : ν.re < s.re) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), spectralSchlafliMellinMixture ν s t x) =
      ((1/2 : ℂ)*(4 : ℂ)^((s-ν)/2)*Complex.Gamma ((s-ν)/2)) *
        ((t : ℂ)^((s+ν)/2-1)*Complex.exp (-(t : ℂ))) := by
  simp only [spectralSchlafliMellinMixture,integral_const_mul]
  rw [complex_gaussian_power_integral (s-ν) (1/(4*t))
    (by simpa only [Complex.sub_re] using sub_pos.mpr hs) (by positivity)]
  have hb : (1/(((1/(4*t) : ℝ) : ℂ))) = (4 : ℂ)*(t : ℂ) := by
    push_cast
    field_simp
  have hm : ((4 : ℂ)*(t : ℂ))^((s-ν)/2) =
      (4 : ℂ)^((s-ν)/2)*(t : ℂ)^((s-ν)/2) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : 0 ≤ (4 : ℝ)) ht.le ((s-ν)/2)
  rw [hb,hm]
  have hp : (t : ℂ)^(ν-1)*(t : ℂ)^((s-ν)/2) = (t : ℂ)^((s+ν)/2-1) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  calc
    _ = ((1/2 : ℂ)*(4 : ℂ)^((s-ν)/2)*Complex.Gamma ((s-ν)/2)) *
        (((t : ℂ)^(ν-1)*(t : ℂ)^((s-ν)/2))*Complex.exp (-(t : ℂ))) := by ring
    _ = _ := by rw [hp]

theorem spectralSchlafliMellinMixture_norm (ν s : ℂ) {t x : ℝ}
    (ht : 0 < t) (hx : 0 < x) :
    ‖spectralSchlafliMellinMixture ν s t x‖ =
      (t^(ν.re-1)*Real.exp (-t)) *
        (x^((s.re-ν.re)-1)*Real.exp (-(1/(4*t))*x^2)) := by
  have he : -((1/(4*t) : ℝ) : ℂ)*(x : ℂ)^2 = (-(1/(4*t))*x^2 : ℝ) := by
    push_cast
    rfl
  simp only [spectralSchlafliMellinMixture,norm_mul,he,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp,Complex.ofReal_re,Complex.neg_re,Complex.sub_re,Complex.one_re]

theorem spectralSchlafliMellinMixture_integral_norm (ν s : ℂ)
    (hs : ν.re < s.re) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), ‖spectralSchlafliMellinMixture ν s t x‖) =
      ((1/2 : ℝ)*(4 : ℝ)^((s.re-ν.re)/2)*Real.Gamma ((s.re-ν.re)/2)) *
        (t^((s.re+ν.re)/2-1)*Real.exp (-t)) := by
  calc
    _ = ∫ x in Ioi (0 : ℝ), (t^(ν.re-1)*Real.exp (-t)) *
        (x^((s.re-ν.re)-1)*Real.exp (-(1/(4*t))*x^2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact spectralSchlafliMellinMixture_norm ν s ht hx
    _ = _ := by
      rw [integral_const_mul,real_gaussian_power_integral (s.re-ν.re) (1/(4*t))
        (sub_pos.mpr hs) (by positivity)]
      have hpow : (1/(4*t) : ℝ)^(-(s.re-ν.re)/2) =
          (4 : ℝ)^((s.re-ν.re)/2)*t^((s.re-ν.re)/2) := by
        rw [show -(s.re-ν.re)/2 = -((s.re-ν.re)/2) by ring,
          Real.rpow_neg_eq_inv_rpow,one_div,inv_inv,
          Real.mul_rpow (by norm_num : 0 ≤ (4 : ℝ)) ht.le]
      rw [hpow]
      have hp : t^(ν.re-1)*t^((s.re-ν.re)/2) = t^((s.re+ν.re)/2-1) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((1/2 : ℝ)*(4 : ℝ)^((s.re-ν.re)/2)*Real.Gamma ((s.re-ν.re)/2)) *
            ((t^(ν.re-1)*t^((s.re-ν.re)/2))*Real.exp (-t)) := by ring
        _ = _ := by rw [hp]

end ArtinMatthews
