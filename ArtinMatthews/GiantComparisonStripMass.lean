module

public import ArtinMatthews.GiantComparisonStripLabels


set_option backward.privateInPublic true
@[expose] public section

/-! The reciprocal of the copied product converts its ordered labels to
their harmonic probability law, leaving one fresh mass for each endpoint. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
  {C : J → Finset (Fin k)}

def giantComparisonSharedMass (c : GiantComparisonSharedLabels P C) : ℝ :=
  giantTwoSidedPatternAuxiliaryMass (C := fun j => univ \ C j) c

theorem giantComparisonSharedMass_sum [DecidableEq J]
    (C : J → Finset (Fin k)) (hV : ∀ j, 0 < bandReciprocalMass (P j)) :
    (∑ c : GiantComparisonSharedLabels P C, giantComparisonSharedMass c) = 1 :=
  giantTwoSidedPatternAuxiliaryMass_sum (fun j => univ \ C j) hV

theorem giantComparisonSlotCard (C : Finset (Fin k)) (ell : ℕ) :
    (univ \ C).card + (ell+C.card) = k+ell := by
  have hc : C.card ≤ k := by
    simpa only [card_univ, Fintype.card_fin] using card_le_card (subset_univ C)
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  omega

theorem giantComparisonSharedMass_eq_div (c : GiantComparisonSharedLabels P C) :
    giantComparisonSharedMass c =
      (∏ j, (bandReciprocalMass (P j))⁻¹^(univ \ C j).card) /
        (giantComparisonSharedProduct c : ℝ) := by
  unfold giantComparisonSharedMass giantTwoSidedPatternAuxiliaryMass giantComparisonSharedProduct
  rw [Nat.cast_prod, ← prod_div_distrib]
  apply prod_congr rfl
  intro j _
  rw [Nat.cast_prod]
  simp only [markedHarmonicAtom, div_eq_mul_inv, one_mul, prod_mul_distrib,
    prod_inv_distrib, prod_const, card_univ, Fintype.card_coe]
  ring

theorem giantComparisonStrip_mass_factor (C : J → Finset (Fin k)) (ell : ℕ)
    (c : GiantComparisonSharedLabels P C) :
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) *
        giantTwoSidedPatternFreshMass P C ell / (giantComparisonSharedProduct c : ℝ) =
      giantComparisonSharedMass c * giantTwoSidedPatternFreshMass P C ell^2 := by
  have hσ : markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) =
      (∏ j, (bandReciprocalMass (P j))⁻¹^(univ \ C j).card) *
        giantTwoSidedPatternFreshMass P C ell := by
    unfold markedPhysicalMass giantTwoSidedPatternFreshMass
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    rw [← pow_add, giantComparisonSlotCard]
  rw [hσ, giantComparisonSharedMass_eq_div]
  ring

end
end ArtinMatthews
