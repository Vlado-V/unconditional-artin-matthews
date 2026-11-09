module

public import ArtinMatthews.GiantSignedStatePermutationEnergy
public import ArtinMatthews.GiantSignedRawEdgeData


set_option backward.privateInPublic true
@[expose] public section

/-! The original endpoint normalization and inverse target permutations
are exactly the full-state slot averages. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedSlotInverse (S B : Type*) (M : ℕ) :
    GiantSignedStateSlotPermutations S B M ≃ GiantSignedStateSlotPermutations S B M where
  toFun π := (fun j => (π.1 j).symm, fun j => (π.2 j).symm)
  invFun π := (fun j => (π.1 j).symm, fun j => (π.2 j).symm)
  left_inv π := by
    rcases π with ⟨πS, πB⟩
    simp only [Equiv.symm_symm]
  right_inv π := by
    rcases π with ⟨πS, πB⟩
    simp only [Equiv.symm_symm]

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem giantSignedStatePermute_inverse
    (π : GiantSignedStateSlotPermutations S B M) (s : GiantSignedState PS PB M) :
    (giantSignedStatePermute PS π.1 π.2).symm s =
      giantSignedStatePermute PS (giantSignedSlotInverse S B M π).1
        (giantSignedSlotInverse S B M π).2 s := rfl

theorem giantSignedStateSlotAverage_inverse
    (f : GiantSignedState PS PB M → ℂ) (s : GiantSignedState PS PB M) :
    (∑ π : GiantSignedStateSlotPermutations S B M,
      (((Fintype.card (GiantSignedStateSlotPermutations S B M) : ℝ)⁻¹ : ℝ) : ℂ) *
        f ((giantSignedStatePermute PS π.1 π.2).symm s)) =
      giantSignedStateSlotAverage PS f s := by
  simp_rw [giantSignedStatePermute_inverse]
  exact (giantSignedSlotInverse S B M).sum_comp
    (fun π => (((Fintype.card (GiantSignedStateSlotPermutations S B M) : ℝ)⁻¹ : ℝ) : ℂ) *
      f (giantSignedStatePermute PS π.1 π.2 s))

theorem giantSignedRawSlotNormalization (M : ℕ) :
    (giantTwoSidedResidueSlotNormalization (J := S) M : ℂ) *
      (giantTwoSidedResidueSlotNormalization (J := B) M : ℂ) =
      (((Fintype.card (GiantSignedStateSlotPermutations S B M) : ℝ)⁻¹ : ℝ) : ℂ)^2 := by
  simp only [giantTwoSidedResidueSlotNormalization, GiantSignedStateSlotPermutations,
    Fintype.card_prod, Nat.cast_mul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_natCast, mul_inv, mul_pow, inv_pow]

end
end ArtinMatthews
