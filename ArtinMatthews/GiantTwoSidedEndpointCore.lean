module

public import ArtinMatthews.GiantCandidateSquareCore
public import ArtinMatthews.GiantCandidateFirstEndpoint


set_option backward.privateInPublic true
@[expose] public section

/-! The actual right endpoint has the ordered-fiber bound at the
stripped product itself. A fixed Dirichlet character retains this
bound, including at nonunits. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateAllocationCore_actual_norm_le_stripped_fiber (γ : ℝ) (hγ : 0 < γ)
    (j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ (C P : Finset ℕ) (n : ℕ),
      ‖giantCandidateAllocationCore C P (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n‖ ≤
        ((giantOrderedProductFiber j (giantCandidateStrip P n)).card:ℝ) := by
  filter_upwards [giantCandidateStrippedSlotCoefficient_actual_norm_le_one γ hγ] with x hx
  intro C P n
  let E := giantOrderedProductFiber j (giantCandidateStrip P n)
  let a := giantCandidateStrippedSlotCoefficient C (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ)
  change ‖∑ t ∈ E,∏ i,a (t i)‖ ≤ _
  calc
    _ ≤ ∑ t ∈ E,‖∏ i,a (t i)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ E,(1:ℝ) := by
      apply sum_le_sum
      intro t _
      rw [norm_prod]
      exact prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hx C (t i))
    _ = _ := by simp only [E,sum_const,nsmul_eq_mul,mul_one]

theorem giantCandidateAllocationCore_character_actual_norm_le_stripped_fiber
    {m : ℕ} (χ : DirichletCharacter ℂ m) (γ : ℝ) (hγ : 0 < γ) (j : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ (C P : Finset ℕ) (n : ℕ),
      ‖χ n*giantCandidateAllocationCore C P (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n‖ ≤
        ((giantOrderedProductFiber j (giantCandidateStrip P n)).card:ℝ) := by
  filter_upwards [giantCandidateAllocationCore_actual_norm_le_stripped_fiber γ hγ j] with x hx
  intro C P n
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (hx C P n)

end
end ArtinMatthews
