module

public import ArtinMatthews.GiantSignedCappedStateDomain


set_option backward.privateInPublic true
@[expose] public section

/-! The retained states give a uniform bound for every projected test. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedStateMemoryCutoff_bound
    {S B : Type*} [Fintype S] [Fintype B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    [Fintype (GiantTwoSidedResidueState PS M)] [∀ g, ∀ p : PB g, NeZero p.val]
    (N : ℕ) (f : GiantSignedState PS PB M → ℂ) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ s, ‖giantSignedStateMemoryCutoff N f s‖ ≤ U := by
  classical
  let : Finite (GiantSignedCappedState PS PB M N) := giantSignedCappedState_finite N
  let := Fintype.ofFinite (GiantSignedCappedState PS PB M N)
  let U := ∑ s : GiantSignedCappedState PS PB M N, ‖f s.1‖
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨U, hU, ?_⟩
  intro s
  by_cases hs : (∑ g, s.2.2.1 g) ≤ N
  · rw [giantSignedStateMemoryCutoff_of_le N f s hs]
    exact Finset.single_le_sum (f := fun t : GiantSignedCappedState PS PB M N => ‖f t.1‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ ⟨s, hs⟩)
  · rw [giantSignedStateMemoryCutoff_of_lt N f s (lt_of_not_ge hs), norm_zero]
    exact hU

end
end ArtinMatthews
