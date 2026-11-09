module

public import ArtinMatthews.MarkedMinorArcBanAdjoint


set_option backward.privateInPublic true
@[expose] public section

/-! The actual fixed compact cutoff supplies all finite row-bound constants. -/
noncomputable section
namespace ArtinMatthews

theorem markedBan_compact_cutoff_constants (ψ : SchwartzMap ℝ ℂ)
    (hc : HasCompactSupport (ψ : ℝ → ℂ)) :
    ∃ A W : ℝ, 1 ≤ A ∧ 1 ≤ W ∧ (∀ u, ‖ψ u‖ ≤ W) ∧
      (∀ u, ψ u ≠ 0 → |u| ≤ A) := by
  obtain ⟨A,hA⟩ := hc.bddAbove_image continuous_norm.continuousOn
  obtain ⟨W,hW⟩ := (hc.isCompact_range ψ.continuous).bddAbove_image continuous_norm.continuousOn
  refine ⟨max 1 A,max 1 W,le_max_left _ _,le_max_left _ _,?_,?_⟩
  · intro u
    exact (hW (Set.mem_image_of_mem norm (Set.mem_range_self u))).trans (le_max_right _ _)
  · intro u hu
    have hh := (hA (Set.mem_image_of_mem norm (subset_tsupport ψ hu))).trans (le_max_right 1 A)
    simpa only [Real.norm_eq_abs] using hh

end ArtinMatthews
