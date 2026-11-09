module

public import ArtinMatthews.SourcePoissonContourInterchange


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

/-- The same summable row majorant controls the absolute integral of the
joint series and the sum of the absolute integrals. -/
theorem sourcePoisson_mul_tsum_integrable_and_summable
    {α ι : Type} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    (K : α → ℂ) (hK : Integrable K μ) (A : ι → α → ℂ)
    (hA : ∀ i, Measurable (A i)) (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i p, ‖A i p‖ ≤ B i) :
    Integrable (fun p => K p * (∑' i, A i p)) μ ∧
      Summable (fun i => ∫ p, ‖K p * A i p‖ ∂μ) := by
  have hnorm (p : α) : Summable (fun i => ‖A i p‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hbound i p) hB
  refine ⟨(hK.norm.mul_const (∑' i, B i)).mono'
    (hK.aestronglyMeasurable.mul (Measurable.tsum hA).aestronglyMeasurable) ?_, ?_⟩
  · filter_upwards with p
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_tsum_le_tsum_norm (hnorm p)).trans
      ((hnorm p).tsum_le_tsum (fun i => hbound i p) hB)
  · have hNonnegInt (i : ι) : 0 ≤ ∫ p, ‖K p * A i p‖ ∂μ :=
      integral_nonneg (fun p => norm_nonneg (K p * A i p))
    refine Summable.of_nonneg_of_le hNonnegInt ?_
      (hB.mul_left (∫ p, ‖K p‖ ∂μ))
    intro i
    rw [← integral_mul_const]
    have hNonneg : ∀ᵐ p ∂μ, 0 ≤ ‖K p * A i p‖ :=
      Filter.Eventually.of_forall (fun p => norm_nonneg (K p * A i p))
    refine integral_mono_of_nonneg hNonneg (hK.norm.mul_const (B i)) ?_
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound i p) (norm_nonneg _)

end
end ArtinMatthews.SourcePhysical
