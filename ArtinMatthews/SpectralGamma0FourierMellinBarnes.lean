module

public import ArtinMatthews.SpectralBesselMellinInversion
public import ArtinMatthews.SpectralWhittakerMellinEvaluation
public import ArtinMatthews.SpectralGamma0NativeFourierBessel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual native Fourier coefficients have the proved Gamma-product
Mellin-Barnes representation.  No extra smoothness or energy input is assumed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

theorem schlafliBesselK_mellin_barnes_integrable (ν : ℂ) (σ : ℝ) (hσ : |ν.re| < σ)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => (x : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I)) *
      spectralKMellinMultiplier ν ((σ : ℂ)+(t : ℂ)*Complex.I)) := by
  have hI := spectralKMellinMultiplier_vertical_integrable ν σ hσ
  have hp : Continuous (fun t : ℝ => (x : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I))) := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    fun_prop
  apply (hI.norm.const_mul (x^(-σ))).mono' (hp.aestronglyMeasurable.mul hI.aestronglyMeasurable)
  filter_upwards [] with t
  simp only [Pi.mul_apply]
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem schlafliBesselK_mellin_barnes (ν : ℂ) (σ : ℝ) (hσ : |ν.re| < σ)
    {x : ℝ} (hx : 0 < x) :
    OAI.CubicEisenstein.schlafliBesselK ν x =
      (1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ)^(-((σ : ℂ)+(t : ℂ)*Complex.I)) *
          ((2 : ℂ)^(((σ : ℂ)+(t : ℂ)*Complex.I)-2) *
            Complex.Gamma ((((σ : ℂ)+(t : ℂ)*Complex.I)-ν)/2) *
            Complex.Gamma ((((σ : ℂ)+(t : ℂ)*Complex.I)+ν)/2)) := by
  have h := (schlafliBesselK_mellin_inversion ν σ hσ hx).symm
  simpa only [mellinInv,spectralKMellinMultiplier,smul_eq_mul] using h

theorem gamma0FullCuspidalSpectralBasis_fourier_mellin_barnes_ae
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (σ : ℝ) (hσ : |(Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))).re| < σ) :
    ∃ a : ℂ, gamma0CuspFourierCoefficient N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)]
      fun y => a*((Real.sqrt y : ℂ)*
        mellinInv σ (spectralKMellinMultiplier
          (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))))
          (|cuspFourierFrequency (N : ℝ) n| * y)) := by
  obtain ⟨a,ha⟩ := gamma0FullCuspidalSpectralBasis_fourier_bessel_ae N i r Y hY n hn
  refine ⟨a,?_⟩
  have hq : 0 < |cuspFourierFrequency (N : ℝ) n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero (N : ℝ) (by exact_mod_cast NeZero.pos N) n hn)
  filter_upwards [ha,ae_restrict_mem measurableSet_Ioi] with y he hy
  rw [he,schlafliBesselK_mellin_inversion _ σ hσ (mul_pos hq (hY.trans hy))]

theorem gamma0FullCuspidalSpectralBasis_fourier_mellin_barnes_canonical_ae
    (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, gamma0CuspFourierCoefficient N r Y hY n
        (gamma0FullCuspidalSpectralBasis N i).val =ᵐ[volume.restrict (Ioi Y)]
      fun y => a*((Real.sqrt y : ℂ)*
        mellinInv (|(Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))).re|+1)
          (spectralKMellinMultiplier (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))))
          (|cuspFourierFrequency (N : ℝ) n| * y)) :=
  gamma0FullCuspidalSpectralBasis_fourier_mellin_barnes_ae N i r Y hY n hn _ (by linarith)

end ArtinMatthews
