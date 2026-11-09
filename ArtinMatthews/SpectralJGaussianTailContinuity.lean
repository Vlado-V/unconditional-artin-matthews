module

public import ArtinMatthews.SpectralJGaussianTailAnalysis
public import ArtinMatthews.SpectralKLDirectL2
public import Mathlib.MeasureTheory.Measure.OpenPos


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ContDiff
noncomputable section

theorem spectralJGaussianTail_continuousOn (F : ℝ → ℂ)
    (hFm : Measurable F) (hF : IntegrableOn F (Ioi (2 : ℝ))) :
    ContinuousOn (spectralJGaussianTail F) (Ioi (0 : ℝ)) := by
  have hi : ContinuousOn (fun Y : ℝ =>
      ∫ w in Ioi (2 : ℝ), (Real.exp (-(Y * w)) : ℂ) * F w) (Ioi (0 : ℝ)) := by
    apply continuousOn_of_dominated
      (F := fun Y w : ℝ => (Real.exp (-(Y * w)) : ℂ) * F w)
      (μ := volume.restrict (Ioi (2 : ℝ))) (bound := fun w => ‖F w‖)
    · intro Y hY
      have he : Measurable (fun w : ℝ => (Real.exp (-(Y * w)) : ℂ)) := by fun_prop
      exact (he.mul hFm).aestronglyMeasurable
    · intro Y hY
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      change 0 < Y at hY
      change 2 < w at hw
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      apply mul_le_of_le_one_left (norm_nonneg _)
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    · exact hF.norm
    · filter_upwards with w
      have hc : Continuous (fun Y : ℝ => (Real.exp (-(Y * w)) : ℂ)) := by fun_prop
      exact (hc.mul continuous_const).continuousOn
  have hp : Continuous (fun Y : ℝ => ((Real.sqrt Y * Real.exp Y : ℝ) : ℂ)) := by fun_prop
  apply (hp.continuousOn.mul hi).congr
  intro Y hY
  exact if_pos hY

theorem spectralKLContinuousPointwiseInverse (G H : ℝ → ℂ)
    (hG : MemLp G 2 spectralKLPhysicalMeasure)
    (hGc : ContinuousOn G (Ioi (0 : ℝ)))
    (hHs : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ))) (hHc : Continuous H)
    (hHr : SpectralKLDirectRapid H)
    (hA : spectralKLAnalysis (hG.toLp G) =ᵐ[spectralKLSpectralMeasure] H) :
    EqOn (spectralKLDirectSynthesis H) G (Ioi (0 : ℝ)) := by
  let hH := spectralKLDirectData_memLp H hHc hHr
  have hAe : spectralKLAnalysis (hG.toLp G) = hH.toLp H := by
    apply Lp.ext
    exact hA.trans hH.coeFn_toLp.symm
  have hi := spectralKLDirectSynthesis_inverse_ae H hHs hHc hHr
  rw [← hAe, spectralKLSynthesis_analysis] at hi
  have ha : spectralKLDirectSynthesis H =ᵐ[spectralKLPhysicalMeasure] G :=
    hi.symm.trans hG.coeFn_toLp
  have hAc : volume.restrict (Ioi (0 : ℝ)) ≪ spectralKLPhysicalMeasure := by
    unfold spectralKLPhysicalMeasure spectralKLPositiveWeightMeasure
    apply withDensity_absolutelyContinuous' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Y hY
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hY)).ne'
  exact Measure.eqOn_open_of_ae_eq (hAc.ae_le ha) isOpen_Ioi
    (spectralKLDirectSynthesis_continuousOn H hHc hHr) hGc

end
end ArtinMatthews
