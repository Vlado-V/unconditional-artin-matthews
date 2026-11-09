module

public import ArtinMatthews.MarkedTypeIIPadCollisions
public import ArtinMatthews.IdealPrimitiveCharacters


set_option backward.privateInPublic true
@[expose] public section

/-! Selected prime labels retain their original harmonic product law.
The index type can be any finite set of selected source slots. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev IdealSelectedLabels {I : Type*} (P : I → Finset ℕ) := ∀ i, ↥(P i)

def idealSelectedMass {I : Type*} [Fintype I] (P : I → Finset ℕ)
    (a : IdealSelectedLabels P) : ℝ :=
  ∏ i, markedHarmonicAtom (P i) (a i)

def idealSelectedProduct {I : Type*} [Fintype I] {P : I → Finset ℕ}
    (a : IdealSelectedLabels P) : ℕ :=
  ∏ i, (a i).val

theorem idealSelectedMass_nonneg {I : Type*} [Fintype I] (P : I → Finset ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (a : IdealSelectedLabels P) :
    0 ≤ idealSelectedMass P a :=
  prod_nonneg fun i _ => markedHarmonicAtom_nonneg (P i) (hV i)

theorem idealSelectedMass_sum {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (hV : ∀ i, 0 < bandReciprocalMass (P i)) :
    (∑ a : IdealSelectedLabels P, idealSelectedMass P a) = 1 := by
  unfold idealSelectedMass
  rw [← Fintype.prod_sum]
  simp only [markedHarmonicAtom_sum _ (hV _), prod_const_one]

theorem idealSelectedProduct_pos {I : Type*} [Fintype I] {P : I → Finset ℕ}
    (hP : ∀ i p, p ∈ P i → p.Prime) (a : IdealSelectedLabels P) :
    0 < idealSelectedProduct a :=
  prod_pos fun i _ => (hP i (a i).val (a i).property).pos

theorem idealSelectedCharacter_product {I : Type*} [Fintype I]
    {P : I → Finset ℕ} {Q : ℕ} (χ : IdealPrimitiveCharacters Q)
    (a : IdealSelectedLabels P) :
    idealPrimitiveCharacterValue χ (idealSelectedProduct a) =
      ∏ i, idealPrimitiveCharacterValue χ (a i).val := by
  unfold idealPrimitiveCharacterValue idealSelectedProduct
  rw [Nat.cast_prod, map_prod]

theorem idealSelectedCharacter_norm_le {I : Type*} [Fintype I]
    {P : I → Finset ℕ} {Q : ℕ} (χ : IdealPrimitiveCharacters Q)
    (a : IdealSelectedLabels P) :
    ‖idealPrimitiveCharacterValue χ (idealSelectedProduct a)‖ ≤ 1 :=
  idealPrimitiveCharacterValue_norm_le χ _

end
end ArtinMatthews
