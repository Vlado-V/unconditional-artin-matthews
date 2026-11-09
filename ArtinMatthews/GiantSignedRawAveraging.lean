module

public import ArtinMatthews.GiantSignedRawEdgeEnumeration
public import ArtinMatthews.GiantSignedStatePermutationEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The original four endpoint permutations and auxiliary tuple have an
exact finite probability law before the actual edge move is selected. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {k ell : ℕ}

abbrev GiantSignedRawOuterChoice (PB : B → Finset ℕ) (C : B → Finset (Fin k)) (ell : ℕ) :=
  GiantSignedStateSlotPermutations S B (k+ell) ×
    GiantSignedStateSlotPermutations S B (k+ell) × GiantTwoSidedPatternAuxiliary PB C

def giantSignedRawOuterWeight {C : B → Finset (Fin k)}
    (i : GiantSignedRawOuterChoice (S := S) PB C ell) : ℝ :=
  giantTwoSidedResidueSlotNormalization (J := S) (k+ell) *
    giantTwoSidedResidueSlotNormalization (J := B) (k+ell) *
      giantTwoSidedPatternAuxiliaryMass i.2.2

theorem giantSignedRawOuterWeight_nonneg {C : B → Finset (Fin k)}
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g))
    (i : GiantSignedRawOuterChoice (S := S) PB C ell) :
    0 ≤ giantSignedRawOuterWeight i :=
  mul_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
    (inv_nonneg.mpr (sq_nonneg _))) (giantTwoSidedPatternAuxiliaryMass_nonneg hVB i.2.2)

theorem giantSignedRawOuterWeight_sum (C : B → Finset (Fin k))
    (hVB : ∀ g, 0 < bandReciprocalMass (PB g)) :
    (∑ i : GiantSignedRawOuterChoice (S := S) PB C ell, giantSignedRawOuterWeight i) = 1 := by
  classical
  have hS : (Fintype.card (S → Equiv.Perm (Fin (k+ell))) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card (B → Equiv.Perm (Fin (k+ell))) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold GiantSignedRawOuterChoice GiantSignedStateSlotPermutations giantSignedRawOuterWeight
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [giantTwoSidedPatternAuxiliaryMass_sum C hVB]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  unfold giantTwoSidedResidueSlotNormalization
  field_simp [hS, hB]

end
end ArtinMatthews
