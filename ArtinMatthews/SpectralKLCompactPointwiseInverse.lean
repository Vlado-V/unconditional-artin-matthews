module

public import ArtinMatthews.SpectralKLDirectL2
public import ArtinMatthews.SpectralKLCompactRapid
public import Mathlib.MeasureTheory.Measure.OpenPos


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter OAI.CubicEisenstein
open scoped ContDiff
noncomputable section

theorem spectralKLCompactOrderTransform_axis_rapid (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    SpectralKLDirectRapid (fun t : ℝ => spectralKLCompactOrderTransform f ((t : ℂ)*Complex.I)) := by
  intro N
  obtain ⟨C,hC,hb⟩ := spectralKLCompactOrderTransform_strip_rapid f hf hc hp N
  refine ⟨C,hC,fun t => ?_⟩
  simpa only [Complex.ofReal_zero,neg_zero,zero_add] using hb 0 t (by norm_num)

theorem spectralKLCompactOrderTransform_axis_smooth (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralKLCompactOrderTransform f ((t : ℂ)*Complex.I)) := by
  have h : ContDiff ℝ ∞ (spectralKLCompactOrderTransform f) :=
    (spectralKLCompactOrderTransform_entire f hf hc hp).contDiff.restrict_scalars ℝ
  have hline : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)*Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact h.comp hline

theorem spectralKLCompactOrderTransform_pointwise_inverse (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) {x : ℝ} (hx : 0 < x) :
    spectralKLWeightedSynthesis
      (fun t : ℝ => spectralKLCompactOrderTransform f ((t : ℂ)*Complex.I)) x = f x := by
  let F : ℝ → ℂ := fun t => spectralKLCompactOrderTransform f ((t : ℂ)*Complex.I)
  have hs : ContDiff ℝ ∞ F := spectralKLCompactOrderTransform_axis_smooth f hf.continuous hc hp
  have hR : SpectralKLDirectRapid F := spectralKLCompactOrderTransform_axis_rapid f hf hc hp
  let hfLp := spectralKLPhysical_compact_memLp f hf.continuous hc hp
  let hFLp := spectralKLDirectData_memLp F hs.continuous hR
  have hA : spectralKLAnalysis (hfLp.toLp f) = hFLp.toLp F := by
    apply Lp.ext
    filter_upwards [spectralKLAnalysis_compact_ae f hf.continuous hc hp, hFLp.coeFn_toLp] with t ht htF
    exact ht.trans ((spectralKLCompactOrderTransform_imaginary f hp t).symm.trans htF.symm)
  have hInv := spectralKLDirectSynthesis_inverse_ae F hs.contDiffOn hs.continuous hR
  rw [← hA,spectralKLSynthesis_analysis] at hInv
  have ha : spectralKLDirectSynthesis F =ᵐ[spectralKLPhysicalMeasure] f :=
    hInv.symm.trans hfLp.coeFn_toLp
  have hAc : volume.restrict (Ioi (0 : ℝ)) ≪ spectralKLPhysicalMeasure := by
    unfold spectralKLPhysicalMeasure spectralKLPositiveWeightMeasure
    apply withDensity_absolutelyContinuous' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hy)).ne'
  have heq := Measure.eqOn_open_of_ae_eq (hAc.ae_le ha) isOpen_Ioi
    (spectralKLDirectSynthesis_continuousOn F hs.continuous hR) hf.continuous.continuousOn
  simpa only [spectralKLDirectSynthesis,ite_eq_left hx,F] using heq hx

end
end ArtinMatthews

