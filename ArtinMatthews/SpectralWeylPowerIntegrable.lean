module

public import ArtinMatthews.SpectralWeylPowerFold
public import ArtinMatthews.SpectralWeylPhysicalContinuity
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute integrability of the actual two-height orbital kernel with
one noncompact power-decaying input and one compact positive-height test. -/

noncomputable section
open Set MeasureTheory Filter
namespace ArtinMatthews

theorem spectralFoldEndpointPower_integrable {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun u : ℝ => (1-u)^(B-1)) (Ioo (0 : ℝ) 1) := by
  have h : IntervalIntegrable (fun u : ℝ => u^(B-1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have ht := h.comp_sub_left 1
  simpa only [sub_zero,sub_self] using ht.2.mono_set Ioo_subset_Ioc_self

theorem spectralWeylFoldDensity_power_integrable {X B M : ℝ}
    (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Integrable (spectralWeylFoldDensity s t f g X) spectralWeylFoldMeasure := by
  obtain ⟨b,hb,hglo⟩ := spectral_compact_positive_lower_bound g hgc hgp
  let C := (4/X)*M*(X^2/(4*b))^B
  have hi := ((spectralKLPhysical_compact_integrable g hg hgc hgp).norm.const_mul C).mul_prod
    (spectralFoldEndpointPower_integrable hB)
  have hpos : ∀ᵐ q ∂spectralWeylFoldMeasure,
      0 < q.1 ∧ q.2 ∈ Ioo (0 : ℝ) 1 := by
    unfold spectralWeylFoldMeasure
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact ⟨hx,hu⟩
  apply hi.mono' (spectralWeylFoldDensity_measurable s t X f g hfm hg.measurable).aestronglyMeasurable
  filter_upwards [hpos] with q hq
  refine (spectralWeylFoldDensity_compact_power_bound hX hb hq.2 hB hB₁ hM s t q.1 hq.1
    f g hf hglo).trans_eq ?_
  dsimp only [C]
  ring

theorem spectralWeylPhysicalIntegrand_power_integrable {X B M : ℝ}
    (hX : 0 < X) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    Integrable (fun q : ℝ × ℝ => spectralWeylPhysicalIntegrand s t f g (q,X))
      (spectralKLPhysicalMeasure.prod spectralKLPhysicalMeasure) :=
  spectralWeylPhysicalIntegrand_integrable_of_fold hX s t f g hfm hg.measurable
    (spectralWeylFoldDensity_power_integrable hX hB hB₁ hM s t f g hfm hg hgc hgp hf)

end ArtinMatthews
