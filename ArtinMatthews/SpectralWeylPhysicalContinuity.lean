module

public import ArtinMatthews.SpectralWeylFoldFiber
public import ArtinMatthews.SpectralWeylFoldDomination


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute fixed-modulus physical integrability and continuity of the
actual compact orbital bilinear.  The folded integral has a fixed
integration domain with a proved local common majorant. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralWeylFoldBilinear (s t : ℝ) (f g : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∫ q : ℝ × ℝ, spectralWeylFoldDensity s t f g X q ∂spectralWeylFoldMeasure

theorem spectralWeylFoldDensity_modulus_continuousAt {X x u : ℝ} (hX : 0 < X) (hx : 0 < x)
    (hu : u ∈ Ioo (0 : ℝ) 1) (s t : ℝ) (f g : ℝ → ℂ) (hf : Continuous f) :
    ContinuousAt (fun V : ℝ => spectralWeylFoldDensity s t f g V (x,u)) X := by
  have hw : 0 < 1-u^2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1+u by linarith [hu.1])]
  unfold spectralWeylFoldDensity spectralWeylFoldHeight
  fun_prop (disch := positivity)

theorem spectralWeylFoldBilinear_continuousOn (s t : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContinuousOn (spectralWeylFoldBilinear s t f g) (Ioi (0 : ℝ)) := by
  intro X hX
  change 0 < X at hX
  obtain ⟨D,hD,hb⟩ := spectralWeylFoldDensity_compact_domination (d := X+1)
    (half_pos hX) s t f g hf hfc hfp hg hgc hgp
  apply ContinuousAt.continuousWithinAt
  unfold spectralWeylFoldBilinear
  apply continuousAt_of_dominated (bound := D)
  · filter_upwards with V
    exact (spectralWeylFoldDensity_measurable s t V f g hf.measurable hg.measurable).aestronglyMeasurable
  · have hN : Icc (X/2) (X+1) ∈ 𝓝 X := Icc_mem_nhds (by linarith) (by linarith)
    filter_upwards [hN] with V hV
    exact hb V hV
  · exact hD
  · have hP : ∀ᵐ q ∂spectralWeylFoldMeasure, 0 < q.1 ∧ q.2 ∈ Ioo (0 : ℝ) 1 := by
      unfold spectralWeylFoldMeasure
      apply (Measure.ae_prod_iff_ae_ae ((measurableSet_lt measurable_const measurable_fst).inter
        (measurable_snd measurableSet_Ioo))).mpr
      filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact ⟨hx,hu⟩
    filter_upwards [hP] with q hq
    exact spectralWeylFoldDensity_modulus_continuousAt hX hq.1 hq.2 s t f g hf

theorem spectralWeylPhysicalIntegrand_integrable_of_fold {X : ℝ} (hX : 0 < X)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hI : Integrable (spectralWeylFoldDensity s t f g X) spectralWeylFoldMeasure) :
    Integrable (fun q : ℝ × ℝ => spectralWeylPhysicalIntegrand s t f g (q,X))
      (spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure) := by
  have hm : Measurable (fun q : ℝ × ℝ => spectralWeylPhysicalIntegrand s t f g (q,X)) :=
    (spectralWeylPhysicalIntegrand_measurable s t f g hfm hgm).comp (measurable_id.prodMk measurable_const)
  change Integrable _ (spectralKLPhysicalMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) at hI
  obtain ⟨hFiber,hNorm⟩ := (integrable_prod_iff hI.aestronglyMeasurable).mp hI
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hFiber,spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hFx hx
    exact (spectralWeylPhysicalFiber_fold_integrable_iff hX hx s t f g).mpr hFx
  · apply hNorm.congr
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    exact (spectralWeylPhysicalFiber_fold_norm_integral hX hx s t f g).symm

theorem spectralWeylPhysicalBilinear_fold {X : ℝ} (hX : 0 < X)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hI : Integrable (spectralWeylFoldDensity s t f g X) spectralWeylFoldMeasure) :
    spectralWeylPhysicalBilinear s t f g X = spectralWeylFoldBilinear s t f g X := by
  have hi := spectralWeylPhysicalIntegrand_integrable_of_fold hX s t f g hfm hgm hI
  change Integrable _ (spectralKLPhysicalMeasure.prod (volume.restrict (Ioo (0 : ℝ) 1))) at hI
  unfold spectralWeylPhysicalBilinear spectralWeylFoldBilinear spectralWeylFoldMeasure
  rw [integral_prod _ hi,integral_prod _ hI]
  apply integral_congr_ae
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
  exact spectralWeylPhysicalFiber_fold_integral hX hx s t f g

theorem spectralWeylPhysicalBilinear_continuousOn (s t : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContinuousOn (spectralWeylPhysicalBilinear s t f g) (Ioi (0 : ℝ)) := by
  apply (spectralWeylFoldBilinear_continuousOn s t f g hf hfc hfp hg hgc hgp).congr
  intro X hX
  exact spectralWeylPhysicalBilinear_fold hX s t f g hf.measurable hg.measurable
    (spectralWeylFoldDensity_compact_integrable hX s t f g hf hfc hfp hg hgc hgp)

end ArtinMatthews
