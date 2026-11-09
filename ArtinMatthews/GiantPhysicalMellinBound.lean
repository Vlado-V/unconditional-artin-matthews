module

public import ArtinMatthews.GiantPhysicalMellin


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Filter MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff
noncomputable section

theorem giantPhysicalMellin_truncated_norm_le {ι : Type*} (edges : Finset ι)
    (A : ι → ℂ) (position dilation : ι → ℝ) (F : SchwartzMap ℝ ℂ)
    {x H R : ℝ} (hx : 0 < x) (hR : 0 ≤ R)
    (hn : ∀ e ∈ edges, 0 < position e) (hD : ∀ e ∈ edges, 0 < dilation e)
    (hbound : ∀ v ∈ Set.Icc (-H) H, ‖giantPhysicalMellinSum edges A position dilation v‖ ≤ R) :
    ‖∫ v : ℝ in Set.Icc (-H) H, F v * primeExtractionMellinPhase (-v) x *
      giantPhysicalMellinSum edges A position dilation v‖ ≤ (∫ v : ℝ, ‖F v‖) * R := by
  calc
    _ ≤ ∫ v : ℝ in Set.Icc (-H) H,
        ‖F v * primeExtractionMellinPhase (-v) x *
          giantPhysicalMellinSum edges A position dilation v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ in Set.Icc (-H) H, ‖F v‖ * R := by
      apply setIntegral_mono_on
        (giantPhysicalMellin_integrable edges A position dilation F hx hn hD).norm.integrableOn
        (F.integrable.norm.mul_const R).integrableOn measurableSet_Icc
      intro v hv
      simp only [norm_mul, primeExtractionMellinPhase_norm, mul_one]
      exact mul_le_mul_of_nonneg_left (hbound v hv) (norm_nonneg _)
    _ ≤ ∫ v : ℝ, ‖F v‖ * R :=
      setIntegral_le_integral (F.integrable.norm.mul_const R)
        (Eventually.of_forall (fun v => mul_nonneg (norm_nonneg _) hR))
    _ = _ := integral_mul_const R _

theorem giantPhysicalMellin_cutoff_norm_le {ι : Type*} (edges : Finset ι)
    (A : ι → ℂ) (position dilation : ι → ℝ) (Ψ : ℝ → ℂ) {a b : ℝ}
    (ha : 0 < a) (hsupp : Function.support Ψ ⊆ Set.Icc a b) (hΨ : ContDiff ℝ ∞ Ψ)
    {x H R : ℝ} (hx : 0 < x) (hH : 0 < H) (hR : 0 ≤ R) (k : ℕ)
    (hn : ∀ e ∈ edges, 0 < position e) (hD : ∀ e ∈ edges, 0 < dilation e)
    (hbound : ∀ v ∈ Set.Icc (-H) H, ‖giantPhysicalMellinSum edges A position dilation v‖ ≤ R) :
    ‖∑ e ∈ edges, A e * Ψ (position e / (x * dilation e))‖ ≤
      (∫ v : ℝ, ‖(𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) v‖) * R +
      ((∫ v : ℝ, |v| ^ k * ‖(𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)) v‖) / H ^ k) *
        ∑ e ∈ edges, ‖A e‖ := by
  let F : SchwartzMap ℝ ℂ := 𝓕 (primeExtractionLogProfile Ψ ha hsupp hΨ)
  let S := ∑ e ∈ edges, A e * Ψ (position e / (x * dilation e))
  let T := ∫ v : ℝ in Set.Icc (-H) H,
    F v * primeExtractionMellinPhase (-v) x * giantPhysicalMellinSum edges A position dilation v
  have htail := giantPhysicalMellin_cutoff_truncation edges A position dilation Ψ ha hsupp hΨ hx hH k hn hD
  have hmain := giantPhysicalMellin_truncated_norm_le edges A position dilation F hx hR hn hD hbound
  calc
    _ ≤ ‖T‖ + ‖S - T‖ := by
      change ‖S‖ ≤ _
      simpa only [add_sub_cancel] using norm_add_le T (S - T)
    _ ≤ _ := add_le_add hmain htail

end
end ArtinMatthews
