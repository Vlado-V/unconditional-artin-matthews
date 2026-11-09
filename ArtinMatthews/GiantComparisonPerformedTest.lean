module

public import ArtinMatthews.GiantComparisonSelectedMarkTest
public import ArtinMatthews.GiantComparisonStripIdeal
public import ArtinMatthews.GiantComparisonAuxiliaryLaw


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized cell character tests depend on the original selected
big slots. The distinguished small group remains free for mark removal. -/
namespace ArtinMatthews
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {x : ℝ} (S : Finset (GiantCandidateGroupIndex x)) {k ell : ℕ}
  (A B D : Finset (GiantCandidatePerformedBig S × Fin k)) (hD : D ⊆ A ∪ B)

private def comparison_test_lift (v : ↥D) : S :=
  giantCandidatePerformedSplitEquiv S (.inr v.val.1)

private def comparison_test_slot (v : ↥D) :
    GiantTwoSidedPatternFreeSlots
      (giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))
        (comparison_test_lift S D v)) ell :=
  Sum.inl ⟨v.val.2, by
    change v.val.2 ∈ idealResidualFreeSlots (A ∪ B) v.val.1
    exact (mem_idealResidualFreeSlots (A ∪ B) v.val.1 v.val.2).mpr (hD v.property)⟩

def giantCandidateComparisonNumberedTest
    (T : IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) D) → ℂ) :
    ((g : S) → Fin (ell+(giantCandidatePerformedPattern S
      (idealResidualCopied (some (A,B))) g).card) → ℕ) → ℂ :=
  giantComparisonNumberedTest
    (P := fun g : S => giantCandidateGroup x g.val)
    (C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))) (ell := ell)
    (comparison_test_lift S D) (comparison_test_slot S A B D hD) T

theorem giantCandidateComparisonNumberedTest_norm_le
    (T : IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) D) → ℂ)
    (hT : ∀ a, ‖T a‖ ≤ 1) (l : (g : S) → Fin (ell+(giantCandidatePerformedPattern S
      (idealResidualCopied (some (A,B))) g).card) → ℕ) :
    ‖giantCandidateComparisonNumberedTest S (ell := ell) A B D hD T l‖ ≤ 1 :=
  giantComparisonNumberedTest_norm_le
    (P := fun g : S => giantCandidateGroup x g.val)
    (C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B))))
    (comparison_test_lift S D) (comparison_test_slot S A B D hD) T hT l

theorem giantCandidateComparisonNumberedTest_small_independent
    (T : IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) D) → ℂ)
    (g : GiantCandidatePerformedSmall S)
    {l l' : (i : S) → Fin (ell+(giantCandidatePerformedPattern S
      (idealResidualCopied (some (A,B))) i).card) → ℕ}
    (he : ∀ i, i ≠ giantCandidatePerformedSplitEquiv S (.inl g) → l i = l' i) :
    giantCandidateComparisonNumberedTest S A B D hD T l =
      giantCandidateComparisonNumberedTest S A B D hD T l' := by
  apply giantComparisonNumberedTest_congr
  intro v
  apply he
  intro h
  have hh : (Sum.inr v.val.1 : GiantCandidatePerformedSmall S ⊕ GiantCandidatePerformedBig S) =
      Sum.inl g := (giantCandidatePerformedSplitEquiv S).injective h
  cases hh

theorem giantCandidateComparisonNumberedTest_free
    (T : IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) D) → ℂ)
    (b : GiantComparisonFreeLabels (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))) ell) :
    giantCandidateComparisonNumberedTest S A B D hD T (giantComparisonNumberedFreeList _ _ ell b) =
      T (giantComparisonSelectedFreeMarking A B D hD
        (fun g => b (giantCandidatePerformedSplitEquiv S (.inr g)))) :=
  giantComparisonNumberedTest_free
    (P := fun g : S => giantCandidateGroup x g.val)
    (C := giantCandidatePerformedPattern S (idealResidualCopied (some (A,B))))
    (comparison_test_lift S D) (comparison_test_slot S A B D hD) T b

end
end ArtinMatthews
