module

public import ArtinMatthews.GiantComparisonFreeMarking
public import ArtinMatthews.GiantComparisonSharedCollision


set_option backward.privateInPublic true
@[expose] public section

/-! The physical guard uses injectivity of each endpoint list and its
literal exclusion of the auxiliary marks. The copied good event and
unshared auxiliary exclusion imply this guard. -/
namespace ArtinMatthews
open Finset
noncomputable section

variable {J : Type*} {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)}

def GiantComparisonUnsharedAuxAvoids (aux : GiantTwoSidedPatternAuxiliary P C)
    (b b' : GiantComparisonFreeLabels P C ell) : Prop :=
  ∀ g j (i : ↥(C g)) (l : GiantTwoSidedPatternFreeSlots (C j) ell),
    (aux g i : ℕ) ≠ (b j l : ℕ) ∧ (aux g i : ℕ) ≠ (b' j l : ℕ)

def GiantComparisonSharedAdmissible (aux : GiantTwoSidedPatternAuxiliary P C)
    (c : GiantComparisonSharedLabels P C) (b b' : GiantComparisonFreeLabels P C ell) : Prop :=
  MarkedPhysicalMarkingDistinct (giantComparisonJoinLabels c b) ∧
  MarkedPhysicalMarkingDistinct (giantComparisonJoinLabels c b') ∧
    ∀ g j (i : ↥(C g)) (l : Fin (k+ell)),
      (aux g i : ℕ) ≠ (giantComparisonJoinLabels c b j l : ℕ) ∧
        (aux g i : ℕ) ≠ (giantComparisonJoinLabels c b' j l : ℕ)

theorem GiantComparisonSharedAdmissible.auxAvoids {aux : GiantTwoSidedPatternAuxiliary P C}
    {c : GiantComparisonSharedLabels P C} {b b' : GiantComparisonFreeLabels P C ell}
    (h : GiantComparisonSharedAdmissible aux c b b') :
    GiantComparisonUnsharedAuxAvoids aux b b' := by
  intro g j i l
  simpa only [giantComparisonJoinLabels_free] using
    h.2.2 g j i (giantTwoSidedPatternFreeSlot (C j) ell l)

theorem giantComparisonSharedAdmissible_of_good
    (aux : GiantTwoSidedPatternAuxiliary P C) {w w' : ℕ}
    (b : GiantComparisonFreeMarking P C ell w) (b' : GiantComparisonFreeMarking P C ell w')
    (haux : GiantComparisonUnsharedAuxAvoids aux b.val b'.val)
    {c : GiantComparisonSharedLabels P C} (hg : GiantComparisonSharedGood aux w w' c) :
    GiantComparisonSharedAdmissible aux c b.val b'.val := by
  refine ⟨?_,?_,?_⟩
  · intro j
    exact (giantComparisonJoinLabels_injective_iff c b.val j).mpr
      ⟨hg.1 j,b.property.1 j,fun i l he => (hg.ne_free b.val b'.val b.property.2 b'.property.2 j j i l).1
        (congrArg Subtype.val he)⟩
  · intro j
    exact (giantComparisonJoinLabels_injective_iff c b'.val j).mpr
      ⟨hg.1 j,b'.property.1 j,fun i l he => (hg.ne_free b.val b'.val b.property.2 b'.property.2 j j i l).2
        (congrArg Subtype.val he)⟩
  · intro g j i l
    obtain ⟨u,rfl⟩ := (giantComparisonSlotEquiv (C j) ell).surjective l
    cases u with
    | inl l =>
      have he := hg.2.2 g j i l
      change (aux g i:ℕ) ≠ (giantComparisonJoinLabels c b.val j (Fin.castAdd ell l.val):ℕ) ∧
        (aux g i:ℕ) ≠ (giantComparisonJoinLabels c b'.val j (Fin.castAdd ell l.val):ℕ)
      simp only [giantComparisonJoinLabels_shared]
      exact ⟨he,he⟩
    | inr l =>
      change (aux g i:ℕ) ≠
          (giantComparisonJoinLabels c b.val j (giantTwoSidedPatternFreeSlot (C j) ell l):ℕ) ∧
        (aux g i:ℕ) ≠ (giantComparisonJoinLabels c b'.val j (giantTwoSidedPatternFreeSlot (C j) ell l):ℕ)
      simpa only [giantComparisonJoinLabels_free] using haux g j i l

end
end ArtinMatthews
