module

public import ArtinMatthews.SourceHyperbolicH1LocalTests
public import Mathlib.Analysis.Normed.Group.Bounded


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open SourceHyperbolicGreen
noncomputable section

/-- Local compact tests have finite global value and native gradient bounds. -/
theorem h1LocalTest_uniform_bounds {ι : Type*} [Fintype ι]
    (U : Set (ProductSpace ι)) (η : h1LocalTests U) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      (∀ x, ‖η.val.val x‖ ≤ M) ∧ (∀ x, productGradientEnergy η.val.val x ≤ B) := by
  obtain ⟨C,hC⟩ := η.val.prop.1.continuous.bounded_above_of_compact_support η.val.prop.2.1
  obtain ⟨D,hD⟩ := (h1GradientAt_continuous η.val).bounded_above_of_compact_support
    (h1GradientAt_compact η.val)
  refine ⟨max C 0, (max D 0) ^ 2, le_max_right _ _, sq_nonneg _, ?_, ?_⟩
  · intro x
    exact (hC x).trans (le_max_left _ _)
  · intro x
    rw [← h1GradientAt_norm_sq η.val x]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hD x).trans (le_max_left _ _)) 2

end
end ArtinMatthews
