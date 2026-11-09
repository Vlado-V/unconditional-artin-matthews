module

public import ArtinMatthews.GiantSignedAuxiliaryCollision


set_option backward.privateInPublic true
@[expose] public section

/-! The original free/active exclusion is equivalent to the coordinate
collision event under the actual disjoint prime groups. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def GiantSignedAuxiliaryBan {J : Type*} {P : J → Finset ℕ} {k M : ℕ}
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P M)
    (aux : GiantTwoSidedPatternAuxiliary P C) : Prop :=
  ∀ g j (i : C g) (l : Fin M),
    (aux g i).val ≠ (a j l).val ∧ (aux g i).val ≠ (b j l).val

theorem giantSignedAuxiliaryBan_iff
    {J : Type*} [DecidableEq J] {P : J → Finset ℕ} {k M : ℕ}
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P M)
    (aux : GiantTwoSidedPatternAuxiliary P C) :
    GiantSignedAuxiliaryBan C a b aux ↔
      ¬∃ e : (Σ g : J, C g) × (Bool × Fin M), giantSignedAuxCollisionEvent C a b e aux := by
  constructor
  · intro h
    rintro ⟨⟨⟨g, i⟩, side, l⟩, he⟩
    cases side
    · exact (h g g i l).1 (congrArg Subtype.val he)
    · exact (h g g i l).2 (congrArg Subtype.val he)
  · intro h g j i l
    by_cases hgj : g = j
    · subst j
      constructor
      · intro he
        apply h
        exact ⟨(⟨g, i⟩, false, l), Subtype.ext he⟩
      · intro he
        apply h
        exact ⟨(⟨g, i⟩, true, l), Subtype.ext he⟩
    · have hd := Finset.disjoint_left.mp (hdis hgj)
      constructor
      · intro he
        exact hd (aux g i).property (he.symm ▸ (a j l).property)
      · intro he
        exact hd (aux g i).property (he.symm ▸ (b j l).property)

theorem giantSignedAuxiliaryBan_probability
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k M : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j))
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (C : J → Finset (Fin k)) (a b : MarkedPhysicalMarking P M) (α : ℝ)
    (hAtom : ∀ j p, markedHarmonicAtom (P j) p ≤ α) :
    (∑ aux : GiantTwoSidedPatternAuxiliary P C,
      idealAuxiliaryMass (fun j => markedHarmonicAtom (P j)) aux *
        (if GiantSignedAuxiliaryBan C a b aux then 0 else 1 : ℝ)) ≤
      ((∑ g, (C g).card) * (2 * M) : ℕ) * α := by
  have he (aux : GiantTwoSidedPatternAuxiliary P C) :
      (if GiantSignedAuxiliaryBan C a b aux then (0 : ℝ) else 1) =
        if ∃ e : (Σ g : J, C g) × (Bool × Fin M), giantSignedAuxCollisionEvent C a b e aux then 1 else 0 := by
    rw [giantSignedAuxiliaryBan_iff hdis]
    split_ifs <;> simp_all
  simp_rw [he]
  have h := giantSignedAuxCollision_probability_le hV C a b α hAtom
  simpa only [giantSignedAuxCollision_index_card] using h

end
end ArtinMatthews
