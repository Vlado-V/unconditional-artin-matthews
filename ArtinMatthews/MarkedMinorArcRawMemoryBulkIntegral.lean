module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkIndices


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite integration over a genuine unordered batch of old indices.
The ordered deleted and surviving coordinates are obtained from the actual
old-index partition, never from a quotient of repeated particle values. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Genuine finite product integration factors over any actual old deletion
subset, with every repeated value and every index multiplicity retained. -/
theorem markedRawMemory_subset_integral {X : Type*} [Fintype X] {k : ℕ}
    (S : Finset (Fin k)) (μ : X → ℂ)
    (f : (Fin S.card → X) → (Fin (Sᶜ).card → X) → ℂ) :
    (∑ a : Fin k → X, (∏ i, μ (a i))*
      f (markedRawSubsetTupleEquiv S a).1 (markedRawSubsetTupleEquiv S a).2)=
      ∑ deleted : Fin S.card → X, ∑ survivors : Fin (Sᶜ).card → X,
        (∏ i, μ (deleted i))*(∏ i, μ (survivors i))*f deleted survivors := by
  classical
  rw [← Equiv.sum_comp (markedRawSubsetTupleEquiv (X := X) S).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro deleted _
  apply Finset.sum_congr rfl
  intro survivors _
  have he := (markedRawSubsetTupleEquiv (X := X) S).apply_symm_apply (deleted,survivors)
  rw [markedRawSubsetTupleEquiv_mass S μ,he]

/-- The true deleted/surviving index partition has exactly the original
number of old indexed particles. -/
theorem markedRawSubsetIndex_card {k : ℕ} (S : Finset (Fin k)) :
    S.card+(Sᶜ).card=k := by
  have hh := Fintype.card_congr (markedRawSubsetIndexEquiv S)
  simpa only [Fintype.card_sum,Fintype.card_fin] using hh

end ArtinMatthews
