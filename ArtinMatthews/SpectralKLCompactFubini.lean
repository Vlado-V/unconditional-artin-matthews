module

public import ArtinMatthews.SpectralKLAnalysisIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute physical/spectral Fubini for genuine compact data. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralKL_compact_pair_integrable (f g : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ =>
      (spectralKLRealKernel p.1 p.2 : ℂ)*g p.1*spectralKLPhysicalCompactDiv f p.2)
      (volume.prod volume) := by
  obtain ⟨C,_,hbound⟩ := spectralKLPhysicalAnalysisIntegral_majorant f hfc hfp
  have hM : Integrable (fun p : ℝ × ℝ => ‖g p.1‖*(C*‖spectralKLPhysicalCompactDiv f p.2‖))
      (volume.prod volume) :=
    (hg.integrable_of_hasCompactSupport hgc).norm.mul_prod
      ((spectralKLPhysicalCompactDiv_integrable f hf hfc hfp).norm.const_mul C)
  have hK : Measurable (fun p : ℝ × ℝ => (spectralKLRealKernel p.1 p.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp spectralKLRealKernel_stronglyMeasurable.measurable
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (spectralKLRealKernel p.1 p.2 : ℂ)*g p.1*spectralKLPhysicalCompactDiv f p.2) (volume.prod volume) :=
    ((hK.mul (hg.measurable.comp measurable_fst)).mul
      ((spectralKLPhysicalCompactDiv_continuous f hf hfp).measurable.comp measurable_snd)).aestronglyMeasurable
  apply hM.mono' hm
  filter_upwards with p
  calc
    _ = ‖g p.1‖*‖(spectralKLRealKernel p.1 p.2 : ℂ)*spectralKLPhysicalCompactDiv f p.2‖ := by
      rw [norm_mul,norm_mul,norm_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound p.1 p.2) (norm_nonneg _)

theorem spectralKL_compact_fubini (f g : ℝ → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (∫ x : ℝ, spectralKLSynthesis g x*spectralKLPhysicalCompactDiv f x) =
      ∫ t : ℝ, g t*spectralKLPhysicalAnalysisIntegral f t := by
  have hI := spectralKL_compact_pair_integrable f g hf hfc hfp hg hgc
  calc
    _ = ∫ x : ℝ, ∫ t : ℝ,
        (spectralKLRealKernel t x : ℂ)*g t*spectralKLPhysicalCompactDiv f x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_mul_const]
      rfl
    _ = ∫ t : ℝ, ∫ x : ℝ,
        (spectralKLRealKernel t x : ℂ)*g t*spectralKLPhysicalCompactDiv f x :=
      (integral_integral_swap hI).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      rw [spectralKLPhysicalAnalysisIntegral,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring

end ArtinMatthews
