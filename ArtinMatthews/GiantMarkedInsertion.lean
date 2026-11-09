module

public import ArtinMatthews.MarkedProgressionResidualBounds


set_option backward.privateInPublic true
@[expose] public section

/-! Inserting a giant prime as an additional selected divisor leaves the
small-band residual unchanged and multiplies its Euler mean by 1/ell. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

theorem marked_insert_selected_sdiff (P S : Finset ℕ) {ell : ℕ} (h : ell ∉ P) :
    insert ell P \ insert ell S = P \ S := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨hp | hp, hn⟩
    · exact (hn (Or.inl hp)).elim
    · exact ⟨hp, fun hs => hn (Or.inr hs)⟩
  · rintro ⟨hp, hn⟩
    exact ⟨Or.inr hp, fun hh => hh.elim (fun heq => h (heq ▸ hp)) hn⟩

theorem marked_insert_selected_active (P S : Finset ℕ) (hS : S ⊆ P) (ell u : ℕ) :
    insert ell S ⊆ activeDivisors (insert ell P) u ↔
      ell ∣ u ∧ S ⊆ activeDivisors P u := by
  constructor
  · intro hs
    refine ⟨(Finset.mem_filter.mp (hs (Finset.mem_insert_self _ _))).2, ?_⟩
    intro p hp
    exact Finset.mem_filter.mpr ⟨hS hp,
      (Finset.mem_filter.mp (hs (Finset.mem_insert_of_mem hp))).2⟩
  · rintro ⟨hdiv, hs⟩ p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hdiv⟩
    · obtain ⟨hpP, hpu⟩ := Finset.mem_filter.mp (hs hp)
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hpP, hpu⟩

theorem markedWeightedResidual_insert_selected (P S : Finset ℕ) (hS : S ⊆ P)
    (θ : ℕ → ℝ) {ell : ℕ} (h : ell ∉ P) (u : ℕ) :
    markedWeightedResidual (insert ell P) (insert ell S) θ u =
      (if ell ∣ u then (1 : ℝ) else 0) * markedWeightedResidual P S θ u := by
  classical
  unfold markedWeightedResidual
  rw [marked_insert_selected_sdiff P S h]
  simp only [marked_insert_selected_active P S hS]
  by_cases hd : ell ∣ u <;> by_cases hs : S ⊆ activeDivisors P u <;> simp [hd, hs]

theorem markedWeightedModel_insert_selected (P S : Finset ℕ) (hS : S ⊆ P)
    (θ : ℕ → ℝ) {ell : ℕ} (h : ell ∉ P) :
    markedWeightedModel (insert ell P) (insert ell S) θ =
      (1 / (ell : ℝ)) * markedWeightedModel P S θ := by
  classical
  have hS' : ell ∉ S := fun hs => h (hS hs)
  simp only [markedWeightedModel, marked_insert_selected_sdiff P S h,
    Finset.prod_insert hS', Nat.cast_mul]
  ring

end ArtinMatthews
