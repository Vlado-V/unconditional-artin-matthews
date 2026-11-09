module

public import ArtinMatthews.SpectralKLMacdonaldUniformNorm
public import ArtinMatthews.SpectralKLMacdonaldCompactPairing


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute physical/spectral interchange for the actual noncompact
Macdonald pairing.  Its compact-height uniform L2 bound is proved from
the positive heat profile, not from an unjustified pointwise K majorant. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

instance spectralKLPhysicalMeasure_sigmaFinite : SigmaFinite spectralKLPhysicalMeasure := by
  unfold spectralKLPhysicalMeasure spectralKLPositiveWeightMeasure
  infer_instance

def spectralKLMacdonaldSpectralPair (y : ℝ) (F g : ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  2*(spectralKLRealKernel q.2 q.1 : ℂ)*(spectralKLRealKernel q.2 y : ℂ)*F q.2*star (g q.1)

theorem spectralKLMacdonaldSpectralPair_measurable (y : ℝ) (F g : ℝ → ℂ)
    (hF : Measurable F) (hg : Measurable g) :
    Measurable (spectralKLMacdonaldSpectralPair y F g) := by
  have hK : Measurable (fun q : ℝ × ℝ => (spectralKLRealKernel q.1 q.2 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp spectralKLRealKernel_stronglyMeasurable.measurable
  unfold spectralKLMacdonaldSpectralPair
  exact (((measurable_const.mul (hK.comp measurable_swap)).mul
    (hK.comp (measurable_snd.prodMk measurable_const))).mul (hF.comp measurable_snd)).mul
      ((continuous_star.measurable.comp hg).comp measurable_fst)

theorem spectralKLMacdonaldRealProduct_memLp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    MemLp (fun r : ℝ => 2*(spectralKLRealKernel r x : ℂ)*(spectralKLRealKernel r y : ℂ))
      2 spectralKLSpectralMeasure := by
  convert spectralKLMacdonaldProduct_memLp hx hy using 1
  funext r
  rw [schlafliBesselK_imaginary_eq_realKernel r hx,schlafliBesselK_imaginary_eq_realKernel r hy]

theorem spectralKLMacdonaldSpectralPair_fiber_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (F g : ℝ → ℂ) (hFm : Measurable F) (hF : MemLp F 2 spectralKLSpectralMeasure) :
    Integrable (fun r : ℝ => spectralKLMacdonaldSpectralPair y F g (x,r)) spectralKLSpectralMeasure := by
  have hH := spectralKLMacdonaldRealProduct_memLp hx hy
  have hi := spectralKL_L2_norm_product_integrable _ F hH hF
  have hm : Measurable (fun r : ℝ => 2*(spectralKLRealKernel r x : ℂ)*
      (spectralKLRealKernel r y : ℂ)*F r) := by
    have hK : Measurable (fun q : ℝ × ℝ => (spectralKLRealKernel q.1 q.2 : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp spectralKLRealKernel_stronglyMeasurable.measurable
    exact ((measurable_const.mul (hK.comp (measurable_id.prodMk measurable_const))).mul
      (hK.comp (measurable_id.prodMk measurable_const))).mul hFm
  have hHF : Integrable (fun r : ℝ => 2*(spectralKLRealKernel r x : ℂ)*
      (spectralKLRealKernel r y : ℂ)*F r) spectralKLSpectralMeasure := by
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards with r
    rw [norm_mul]
  exact hHF.mul_const (star (g x))

theorem spectralKLMacdonaldSpectralPair_integrable {y : ℝ} (hy : 0 < y)
    (F g : ℝ → ℂ) (hFm : Measurable F) (hF : MemLp F 2 spectralKLSpectralMeasure)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    Integrable (spectralKLMacdonaldSpectralPair y F g) (spectralKLPhysicalMeasure.prod spectralKLSpectralMeasure) := by
  have hm : AEStronglyMeasurable (spectralKLMacdonaldSpectralPair y F g)
      (spectralKLPhysicalMeasure.prod spectralKLSpectralMeasure) :=
    (spectralKLMacdonaldSpectralPair_measurable y F g hFm hg.measurable).aestronglyMeasurable
  obtain ⟨a,ha,hax⟩ := spectral_compact_positive_lower_bound g hgc hgp
  let B : ℝ := ‖(spectralKLExpReciprocal_memLp (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 < a*y/2)).toLp (spectralKLExpReciprocal 1 (a*y/2))‖^2+‖hF.toLp F‖^2
  have hgI := (spectralKLPhysical_compact_integrable g hg hgc hgp).norm.const_mul B
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    exact spectralKLMacdonaldSpectralPair_fiber_integrable hx hy F g hFm hF
  · apply hgI.mono' hm.norm.integral_prod_right'
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    by_cases hg0 : g x = 0
    · simp only [spectralKLMacdonaldSpectralPair,hg0,star_zero,mul_zero,norm_zero,integral_zero,le_refl]
    · have hax' := hax x (subset_tsupport g hg0)
      have hnorm : (∫ r : ℝ, ‖spectralKLMacdonaldSpectralPair y F g (x,r)‖ ∂spectralKLSpectralMeasure) =
          (∫ r : ℝ, ‖2*schlafliBesselK ((r : ℂ)*Complex.I) x*
            schlafliBesselK ((r : ℂ)*Complex.I) y‖*‖F r‖ ∂spectralKLSpectralMeasure)*‖g x‖ := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with r
        rw [spectralKLMacdonaldSpectralPair,norm_mul,norm_mul,norm_star,
          schlafliBesselK_imaginary_eq_realKernel r hx,schlafliBesselK_imaginary_eq_realKernel r hy]
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right (spectralKLMacdonaldProduct_uniform_pair_bound ha hy hax' F hF) (norm_nonneg _)

theorem spectralKLMacdonaldSpectralPair_swap {y : ℝ} (hy : 0 < y)
    (F g : ℝ → ℂ) (hFm : Measurable F) (hF : MemLp F 2 spectralKLSpectralMeasure)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    (∫ x : ℝ, (∫ r : ℝ, spectralKLMacdonaldSpectralPair y F g (x,r)
      ∂spectralKLSpectralMeasure) ∂spectralKLPhysicalMeasure) =
      ∫ r : ℝ, (∫ x : ℝ, spectralKLMacdonaldSpectralPair y F g (x,r)
        ∂spectralKLPhysicalMeasure) ∂spectralKLSpectralMeasure :=
  integral_integral_swap (spectralKLMacdonaldSpectralPair_integrable hy F g hFm hF hg hgc hgp)

end ArtinMatthews
