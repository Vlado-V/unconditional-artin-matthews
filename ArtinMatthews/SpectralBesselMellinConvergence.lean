module

public import ArtinMatthews.SpectralSchlafliMellinMixture


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence and Fubini for the actual arbitrary-order K Mellin
integral.  The hypotheses are the two genuine Gamma half-planes. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralSchlafliMellinMixture_integrable (ν s : ℂ)
    (hminus : ν.re < s.re) (hplus : -ν.re < s.re) :
    Integrable (fun p : ℝ × ℝ => spectralSchlafliMellinMixture ν s p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => spectralSchlafliMellinMixture ν s p.1 p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    unfold spectralSchlafliMellinMixture
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact spectralSchlafliMellinMixture_slice_integrable ν s hminus ht
  · have hg := (Real.GammaIntegral_convergent
        (show 0 < (s.re+ν.re)/2 by linarith)).const_mul
        ((1/2 : ℝ)*(4 : ℝ)^((s.re-ν.re)/2)*Real.Gamma ((s.re-ν.re)/2))
    apply hg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [spectralSchlafliMellinMixture_integral_norm ν s hminus ht]
    ring

theorem spectralSchlafliMellinMixture_integral_t (ν s : ℂ) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), spectralSchlafliMellinMixture ν s t x) =
      (x : ℂ)^((s-ν)-1)*schlafliIntegral ν x := by
  rw [schlafliIntegral,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have he : Complex.exp (-(t : ℂ))*Complex.exp (-((1/(4*t) : ℝ) : ℂ)*(x : ℂ)^2) =
      Complex.exp (-(t : ℂ)-(x : ℂ)^2/(4*t)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  unfold spectralSchlafliMellinMixture
  linear_combination (t : ℂ)^(ν-1)*(x : ℂ)^((s-ν)-1)*he

theorem schlafliBesselK_mellin_mixture (ν s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ)^(s-1)*schlafliBesselK ν x =
      ((1/2 : ℂ)*(2 : ℂ)^ν)*(∫ t in Ioi (0 : ℝ), spectralSchlafliMellinMixture ν s t x) := by
  rw [schlafliBesselK,spectralSchlafliMellinMixture_integral_t]
  have hdiv : (x/2 : ℂ)^(-ν) = (x : ℂ)^(-ν)/(2 : ℂ)^(-ν) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.div_cpow_ofReal_nonneg hx.le (by norm_num : 0 ≤ (2 : ℝ)) (-ν)
  rw [hdiv,Complex.cpow_neg (2 : ℂ) ν,div_inv_eq_mul]
  have hp : (x : ℂ)^(s-1)*(x : ℂ)^(-ν) = (x : ℂ)^((s-ν)-1) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 1
    ring
  linear_combination (1/2 : ℂ)*(2 : ℂ)^ν*schlafliIntegral ν x*hp

theorem schlafliBesselK_mellin_integrable_halves (ν s : ℂ)
    (hminus : ν.re < s.re) (hplus : -ν.re < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*schlafliBesselK ν x) (Ioi 0) := by
  apply ((spectralSchlafliMellinMixture_integrable ν s hminus hplus).integral_prod_right.const_mul
    ((1/2 : ℂ)*(2 : ℂ)^ν)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (schlafliBesselK_mellin_mixture ν s hx).symm

theorem schlafliBesselK_mellin_integrable (ν s : ℂ) (hs : |ν.re| < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*schlafliBesselK ν x) (Ioi 0) :=
  schlafliBesselK_mellin_integrable_halves ν s
    (lt_of_le_of_lt (le_abs_self _) hs) (lt_of_le_of_lt (neg_le_abs _) hs)

end ArtinMatthews
