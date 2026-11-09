module

public import ArtinMatthews.GiantSignedStatePermutationEnergy
public import ArtinMatthews.IdealSlotPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The original tilted active product mass permits exact source slot
reindexing against a symmetric test, with no normalization of the law. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedActiveSlotPairing_fixed {B : Type*} [Fintype B] [DecidableEq B]
    {PB : B → Finset ℕ} {M : ℕ} (ν : ∀ g, PB g → ℝ)
    (f g : MarkedPhysicalMarking PB M → ℂ) (hf : IdealSymmetric f) :
    (∑ a, (giantSignedActiveMass ν a : ℂ) * star (f a) * idealSlotAverage g a) =
      ∑ a, (giantSignedActiveMass ν a : ℂ) * star (f a) * g a := by
  let A := MarkedPhysicalMarking PB M
  let P := B → Equiv.Perm (Fin M)
  let W : ℂ := (Fintype.card P : ℂ)⁻¹
  let F (a : A) : ℂ := (giantSignedActiveMass ν a : ℂ) * star (f a) * g a
  have hperm (π : P) : (∑ a : A, (giantSignedActiveMass ν a : ℂ) * star (f a) *
      g (giantTwoSidedPermuteLabels π a)) = ∑ a : A, F a := by
    have h := (giantSignedGroupedTuplePermutation π).sum_comp F
    have he (a : A) : giantSignedGroupedTuplePermutation π a = giantTwoSidedPermuteLabels π a := rfl
    have hm (a : A) : giantSignedActiveMass ν (giantTwoSidedPermuteLabels π a) =
        giantSignedActiveMass ν a := giantSignedActiveMass_slot_permute ν π a
    have hfun (a : A) : f (giantTwoSidedPermuteLabels π a) = f a := hf π a
    simpa only [F, he, hm, hfun] using h
  calc
    _ = ∑ a : A, ∑ π : P, W * ((giantSignedActiveMass ν a : ℂ) * star (f a) *
        g (giantTwoSidedPermuteLabels π a)) := by
      unfold idealSlotAverage
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro π _
      dsimp only [W]
      ring
    _ = ∑ π : P, ∑ a : A, W * ((giantSignedActiveMass ν a : ℂ) * star (f a) *
        g (giantTwoSidedPermuteLabels π a)) := Finset.sum_comm
    _ = ∑ π : P, W * ∑ a : A, F a := by simp only [← Finset.mul_sum, hperm]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, W]
      have hP : (Fintype.card P : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [← mul_assoc, mul_inv_cancel₀ hP, one_mul]

end
end ArtinMatthews
