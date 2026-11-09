module

public import ArtinMatthews.ShiftedPairGrouping


set_option backward.privateInPublic true
@[expose] public section

/-! The complete arithmetic summations of the two off-diagonal weights,
over the literal source pairs. The analytic correlation estimate is separate.
-/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem shiftedOffDiagonal_first_weight (ε : ℝ) (hε : 0<ε) (hsmall : ε<1/2) :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℕ,
      (∑ p ∈ shiftedSourcePairs B,
        (shiftedCommonPrimePart p.1 p.2 : ℝ) / Real.sqrt (p.1.gcd p.2)) ≤
      C*(B : ℝ)^(2+ε) := by
  obtain ⟨C,hC,hsum⟩ := shiftedActualPairs_first_contribution ε hε hsmall
  refine ⟨C,hC,?_⟩
  intro B
  rw [shiftedSourcePairs_sum_grouped B (fun d D => (D : ℝ)/Real.sqrt d)]
  simpa only [div_eq_mul_inv,mul_assoc] using hsum B

theorem shiftedOffDiagonal_second_weight (ε : ℝ) (hε : 0<ε) (hsmall : ε<3/4) :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℕ,
      (∑ p ∈ shiftedSourcePairs B,
        (shiftedCommonPrimePart p.1 p.2 : ℝ)^(1/4 : ℝ)) ≤
      C*(B : ℝ)^(2+ε) := by
  obtain ⟨C,hC,hsum⟩ := shiftedActualPairs_second_contribution ε hε hsmall
  refine ⟨C,hC,?_⟩
  intro B
  rw [shiftedSourcePairs_sum_grouped B (fun _d D => (D : ℝ)^(1/4 : ℝ))]
  exact hsum B

end ArtinMatthews
