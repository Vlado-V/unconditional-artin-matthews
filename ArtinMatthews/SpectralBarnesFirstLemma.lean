module

public import ArtinMatthews.SpectralBetaFourierGamma
public import ArtinMatthews.SpectralFourierProductPairing


set_option backward.privateInPublic true
@[expose] public section

/-! Barnes' first lemma from the genuine beta log profiles, Fourier
inversion and a proved L1 Fubini pairing. -/

noncomputable section
open Set MeasureTheory Filter
open scoped FourierTransform

namespace ArtinMatthews

theorem spectral_beta_fourier_product (a b c d : ℂ)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (∫ ξ : ℝ, Complex.betaIntegral (a-(2*Real.pi*ξ : ℝ)*Complex.I) (b+(2*Real.pi*ξ : ℝ)*Complex.I) *
      Complex.betaIntegral (c-(2*Real.pi*ξ : ℝ)*Complex.I) (d+(2*Real.pi*ξ : ℝ)*Complex.I)) =
        Complex.betaIntegral (a+d) (b+c) := by
  calc
    _ = ∫ ξ : ℝ, 𝓕 (spectralBetaLogProfile a b) ξ * 𝓕 (spectralBetaLogProfile c d) ξ := by
      simp only [spectralBetaLogProfile_fourier]
    _ = ∫ u : ℝ, spectralBetaLogProfile a b u * spectralBetaLogProfile c d (-u) :=
      spectral_fourier_product_pairing _ _ (spectralBetaLogProfile_integrable a b ha hb)
        (spectralBetaLogProfile_integrable c d hc hd)
        (spectralBetaLogProfile_fourier_integrable c d hc hd) (spectralBetaLogProfile_continuous c d)
    _ = _ := by
      simp only [spectralBetaLogProfile_reflect_product,spectralBetaLogProfile_integral]

theorem spectral_beta_fourier_product_integrable (a b c d : ℂ)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable (fun ξ : ℝ =>
      Complex.betaIntegral (a-(2*Real.pi*ξ : ℝ)*Complex.I) (b+(2*Real.pi*ξ : ℝ)*Complex.I) *
      Complex.betaIntegral (c-(2*Real.pi*ξ : ℝ)*Complex.I) (d+(2*Real.pi*ξ : ℝ)*Complex.I)) := by
  have h := (spectralFourierPairKernel_integrable (spectralBetaLogProfile a b)
    (𝓕 (spectralBetaLogProfile c d)) (spectralBetaLogProfile_integrable a b ha hb)
    (spectralBetaLogProfile_fourier_integrable c d hc hd)).integral_prod_right
  apply h.congr
  filter_upwards [] with ξ
  rw [spectralFourierPairKernel_integral_x,spectralBetaLogProfile_fourier,spectralBetaLogProfile_fourier]

def spectralBarnesIntegrand (a b c d : ℂ) (t : ℝ) : ℂ :=
  Complex.Gamma (a+(t : ℂ)*Complex.I) * Complex.Gamma (b+(t : ℂ)*Complex.I) *
    Complex.Gamma (c-(t : ℂ)*Complex.I) * Complex.Gamma (d-(t : ℂ)*Complex.I)

theorem spectralBarnesIntegrand_beta (a b c d : ℂ)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) (t : ℝ) :
    spectralBarnesIntegrand a b c d t =
      (Complex.Gamma (a+c)*Complex.Gamma (b+d)) *
        (Complex.betaIntegral (c-(t : ℂ)*Complex.I) (a+(t : ℂ)*Complex.I) *
          Complex.betaIntegral (d-(t : ℂ)*Complex.I) (b+(t : ℂ)*Complex.I)) := by
  have h1 := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (show 0 < (c-(t : ℂ)*Complex.I).re by simpa using hc)
    (show 0 < (a+(t : ℂ)*Complex.I).re by simpa using ha)
  have h2 := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (show 0 < (d-(t : ℂ)*Complex.I).re by simpa using hd)
    (show 0 < (b+(t : ℂ)*Complex.I).re by simpa using hb)
  rw [show c-(t : ℂ)*Complex.I+(a+(t : ℂ)*Complex.I) = a+c by ring] at h1
  rw [show d-(t : ℂ)*Complex.I+(b+(t : ℂ)*Complex.I) = b+d by ring] at h2
  unfold spectralBarnesIntegrand
  calc
    _ = (Complex.Gamma (c-(t : ℂ)*Complex.I)*Complex.Gamma (a+(t : ℂ)*Complex.I)) *
        (Complex.Gamma (d-(t : ℂ)*Complex.I)*Complex.Gamma (b+(t : ℂ)*Complex.I)) := by ring
    _ = _ := by rw [h1,h2]; ring

theorem spectralBarnesIntegrand_integrable (a b c d : ℂ)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable (spectralBarnesIntegrand a b c d) := by
  have h := (spectral_beta_fourier_product_integrable c a d b hc ha hd hb).const_mul
    (Complex.Gamma (a+c)*Complex.Gamma (b+d))
  have hscale : Integrable (fun ξ : ℝ => spectralBarnesIntegrand a b c d ((2*Real.pi)*ξ)) := by
    apply h.congr
    filter_upwards [] with ξ
    exact (spectralBarnesIntegrand_beta a b c d ha hb hc hd ((2*Real.pi)*ξ)).symm
  exact (integrable_comp_mul_left_iff _ (by positivity : 2*Real.pi ≠ 0)).mp hscale

theorem spectral_barnes_first_lemma (a b c d : ℂ)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (1/(2*Real.pi) : ℝ) • (∫ t : ℝ, spectralBarnesIntegrand a b c d t) =
      Complex.Gamma (a+c)*Complex.Gamma (a+d)*Complex.Gamma (b+c)*Complex.Gamma (b+d) /
        Complex.Gamma (a+b+c+d) := by
  have hscale := Measure.integral_comp_mul_left (spectralBarnesIntegrand a b c d) (2*Real.pi)
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2*Real.pi))] at hscale
  rw [one_div,← hscale]
  simp_rw [spectralBarnesIntegrand_beta a b c d ha hb hc hd]
  rw [integral_const_mul,spectral_beta_fourier_product c a d b hc ha hd hb,
    Complex.betaIntegral_eq_Gamma_mul_div (c+b) (a+d) (by simpa using add_pos hc hb) (by simpa using add_pos ha hd)]
  rw [show c+b+(a+d) = a+b+c+d by ring,show c+b = b+c by ring]
  ring

end ArtinMatthews
