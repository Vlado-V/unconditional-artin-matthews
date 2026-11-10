module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Set


set_option backward.privateInPublic true
@[expose] public section

/-! Integrability and mass control from a finite measurable cover. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

/-- A finite measurable cover by integrable pieces proves integrability on the
covered set and the expected bound, without requiring disjointness. -/
theorem finite_cover_integrable_integral_le_sum {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (S : ι → Set α) {K : Set α}
    (hK : MeasurableSet K) (hS : ∀ i ∈ s, MeasurableSet (S i))
    (hcover : K ⊆ ⋃ i ∈ s, S i) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hm : AEStronglyMeasurable f μ) (hi : ∀ i ∈ s, IntegrableOn f (S i) μ) :
    IntegrableOn f K μ ∧ (∫ x in K, f x ∂μ) ≤ ∑ i ∈ s, ∫ x in S i, f x ∂μ := by
  classical
  have hIi (i : ι) (h : i ∈ s) : Integrable ((S i).indicator f) μ :=
    (integrable_indicator_iff (hS i h)).mpr (hi i h)
  have hpoint (x : α) : K.indicator f x ≤ ∑ i ∈ s, (S i).indicator f x := by
    by_cases hx : x ∈ K
    · obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hcover hx)
      rw [indicator_of_mem hx]
      calc
        f x = (S i).indicator f x := (indicator_of_mem hxi f).symm
        _ ≤ ∑ j ∈ s, (S j).indicator f x := Finset.single_le_sum
          (fun j _ => indicator_nonneg (fun _ _ => hf _) _) his
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun i _ => indicator_nonneg (fun _ _ => hf _) _)
  have hsum : Integrable (fun x => ∑ i ∈ s, (S i).indicator f x) μ :=
    integrable_finsetSum s hIi
  have hki : Integrable (K.indicator f) μ := by
    apply hsum.mono' (hm.indicator hK)
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => hf _) _)]
      exact hpoint x)
  refine ⟨(integrable_indicator_iff hK).mp hki, ?_⟩
  calc
    (∫ x in K, f x ∂μ) = ∫ x, K.indicator f x ∂μ := (integral_indicator hK).symm
    _ ≤ ∫ x, ∑ i ∈ s, (S i).indicator f x ∂μ := integral_mono hki hsum hpoint
    _ = ∑ i ∈ s, ∫ x in S i, f x ∂μ := by
      rw [integral_finsetSum s hIi]
      apply Finset.sum_congr rfl
      exact fun i h => integral_indicator (hS i h)

end ArtinMatthews
