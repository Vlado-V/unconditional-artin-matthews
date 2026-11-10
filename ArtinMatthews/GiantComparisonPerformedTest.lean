module

public import ArtinMatthews.GiantComparisonSelectedMarkTest
public import ArtinMatthews.GiantComparisonStripIdeal
public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
