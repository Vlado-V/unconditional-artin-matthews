module

public import ArtinMatthews.SpectralKLDirectSmallBound
public import ArtinMatthews.SpectralKLDirectL2
public import ArtinMatthews.SpectralKLWindowContinuation


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter Complex OAI.CubicEisenstein
open scoped ContDiff ComplexConjugate
noncomputable section

theorem spectralKLDirectSynthesis_real (F : ℝ → ℂ)
    (hF : ∀ t : ℝ, star (F t) = F t) (x : ℝ) :
    star (spectralKLDirectSynthesis F x) = spectralKLDirectSynthesis F x := by
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
    change conj (r : ℂ) = (r : ℂ)
    exact conj_ofReal r
  rw [spectralKLDirectSynthesis]
  by_cases hx : 0 < x
  · rw [ite_eq_left hx, spectralKLWeightedSynthesis]
    change conj _ = _
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [schlafliBesselK_imaginary_eq_realKernel t hx]
    simpa only [map_mul, conj_ofReal, starRingEnd_apply, hreal] using congrArg
      (fun z : ℂ => (spectralKLRealKernel t x : ℂ) * z * (spectralKLPlancherelWeight t : ℂ)) (hF t)
  · simp only [ite_eq_right hx, star_zero]

theorem spectralKLDirectSynthesis_analysis_pointwise (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => F (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F) :
    ∀ t : ℝ, spectralKLPhysicalAnalysisIntegral
      (spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))) t = F (t : ℂ) := by
  let f : ℝ → ℂ := spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hzB : z.im ≤ 3 / 4) :=
    hhol z (by rw [abs_of_nonneg hz0]; exact hzB)
  have hR := spectralKLDirectStripRapid_real hrapid
  obtain ⟨M, hM, hpower⟩ := spectralKLDirectSynthesis_global_power_bound F heven hh hrapid
  have hfm : Measurable f := spectralKLDirectSynthesis_measurable _ hsmooth.continuous hR
  have hfLp : MemLp f 2 spectralKLPhysicalMeasure :=
    spectralKLDirectSynthesis_memLp _ hsmooth.contDiffOn hsmooth.continuous hR
  have hFLp := spectralKLDirectData_memLp _ hsmooth.continuous hR
  have hInv := spectralKLDirectSynthesis_inverse_ae _ hsmooth.contDiffOn hsmooth.continuous hR
  have hEq : hfLp.toLp f = spectralKLCompletedSynthesis (hFLp.toLp (fun t : ℝ => F (t : ℂ))) := by
    apply Lp.ext
    exact hfLp.coeFn_toLp.trans hInv.symm
  have hAnalysis : spectralKLAnalysis (hfLp.toLp f) =ᵐ[spectralKLSpectralMeasure]
      (fun t : ℝ => F (t : ℂ)) := by
    rw [hEq, spectralKLAnalysis_synthesis]
    exact hFLp.coeFn_toLp
  apply spectralKLPower_analysis_eq f (fun t : ℝ => F (t : ℂ)) hfm
    (fun x hx => by simp only [f, spectralKLDirectSynthesis, ite_eq_right (not_lt.mpr hx)]) hfLp
    M (3 / 4) hM (by norm_num) hpower hsmooth.continuous
    (fun t => by simpa only [Complex.ofReal_neg] using heven (t : ℂ)) hAnalysis

theorem spectralKLDirectSynthesis_continued_transform (F : ℂ → ℂ)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hsmooth : ContDiff ℝ ∞ (fun t : ℝ => F (t : ℂ)))
    (hhol : ∀ z : ℂ, |z.im| ≤ 3 / 4 → DifferentiableAt ℂ F z)
    (hrapid : SpectralKLDirectStripRapid F)
    (ν : ℂ) (hν : |ν.re| ≤ 1 / 2) :
    spectralKLCompactOrderTransform (spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))) ν = F (-I * ν) := by
  let f : ℝ → ℂ := spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))
  have hh (z : ℂ) (hz0 : 0 ≤ z.im) (hzB : z.im ≤ 3 / 4) :=
    hhol z (by rw [abs_of_nonneg hz0]; exact hzB)
  have hR := spectralKLDirectStripRapid_real hrapid
  obtain ⟨M, hM, hpower⟩ := spectralKLDirectSynthesis_global_power_bound F heven hh hrapid
  have hfm : Measurable f := spectralKLDirectSynthesis_measurable _ hsmooth.continuous hR
  have hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0 :=
    fun x hx => by simp only [f, spectralKLDirectSynthesis, ite_eq_right (not_lt.mpr hx)]
  apply spectral_half_strip_identity (spectralKLCompactOrderTransform f) (fun μ => F (-I * μ)) ?_ ?_ ?_ ν hν
  · intro μ hμ
    exact (spectralKLPowerOrderTransform_hasDerivAt f hfm hfzero M hM hpower μ hμ).differentiableAt
  · intro μ hμ
    have hs : |(-I * μ).im| ≤ 3 / 4 := by
      simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_add, abs_neg]
      exact hμ.trans (by norm_num)
    exact (hhol _ hs).comp μ ((hasDerivAt_id μ).const_mul (-I)).differentiableAt
  · intro t
    rw [spectralKLPowerOrderTransform_imaginary _ hfzero]
    change spectralKLPhysicalAnalysisIntegral
      (spectralKLDirectSynthesis (fun t : ℝ => F (t : ℂ))) t = _
    rw [spectralKLDirectSynthesis_analysis_pointwise F heven hsmooth hhol hrapid]
    have ht : -I * ((t : ℂ) * I) = (t : ℂ) := by linear_combination -(t : ℂ) * I_sq
    rw [ht]

end
end ArtinMatthews
