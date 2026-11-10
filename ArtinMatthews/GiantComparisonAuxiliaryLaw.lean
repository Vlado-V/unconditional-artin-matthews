module

public import ArtinMatthews.IdealAuxiliarySelected
public import ArtinMatthews.IdealSelectedUnion
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

/-! Small bands have no auxiliary slots. On the two disjoint big probe
sets, the performed auxiliary law is the original product of the two
selected harmonic laws. Its tests may keep every physical exclusion. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section

variable {x : ℝ} (S : Finset (GiantCandidateGroupIndex x)) {k : ℕ}

def giantCandidatePerformedAuxiliaryEquiv (C : GiantCandidatePerformedBig S → Finset (Fin k)) :
    GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S C) ≃
    GiantTwoSidedPatternAuxiliary (giantCandidatePerformedBigBand S) C where
  toFun aux g := aux (giantCandidatePerformedSplitEquiv S (.inr g))
  invFun aux := fun
    | ⟨.inl _, _⟩ => fun i => False.elim (notMem_empty _ i.property)
    | ⟨.inr g, hg⟩ => aux ⟨g,hg⟩
  left_inv aux := by
    funext g i
    rcases g with ⟨g|g, hg⟩
    · exact False.elim (notMem_empty _ i.property)
    · rfl
  right_inv aux := rfl

theorem giantCandidatePerformedAuxiliary_prod {R : Type*} [CommMonoid R]
    (C : GiantCandidatePerformedBig S → Finset (Fin k))
    (F : (g : S) → ↥(giantCandidateGroup x g.val) → R)
    (aux : GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S C)) :
    (∏ g : S, ∏ i : ↥(giantCandidatePerformedPattern S C g), F g (aux g i)) =
      ∏ g : GiantCandidatePerformedBig S, ∏ i : ↥(C g),
        F (giantCandidatePerformedSplitEquiv S (.inr g)) (giantCandidatePerformedAuxiliaryEquiv S C aux g i) := by
  let f (g : S) := ∏ i : ↥(giantCandidatePerformedPattern S C g), F g (aux g i)
  let e := giantCandidatePerformedSplitEquiv S
  have hsmall (g : GiantCandidatePerformedSmall S) : f (e (.inl g)) = 1 := by
    apply prod_eq_one
    intro i _
    exact False.elim (notMem_empty _ i.property)
  have h := e.prod_comp f
  rw [Fintype.prod_sum_type] at h
  simp only [hsmall, prod_const_one, one_mul] at h
  exact h.symm

def giantCandidatePerformedAuxiliarySplit (A B : Finset (GiantCandidatePerformedBig S × Fin k))
    (hAB : Disjoint A B) :
    GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))) ≃
      IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) A) ×
        IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) B) :=
  (giantCandidatePerformedAuxiliaryEquiv S (idealResidualFreeSlots (A ∪ B))).trans
    ((idealAuxiliarySelectedEquiv (giantCandidatePerformedBigBand S) (A ∪ B)).trans
      (idealSelectedUnionEquiv (giantCandidatePerformedBigBand S) A B hAB))

theorem giantCandidatePerformedAuxiliarySplit_product (A B : Finset (GiantCandidatePerformedBig S × Fin k))
    (hAB : Disjoint A B)
    (aux : GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S (idealResidualCopied (some (A,B))))) :
    giantTwoSidedPatternAuxiliaryProduct aux =
      idealSelectedProduct (giantCandidatePerformedAuxiliarySplit S A B hAB aux).1 *
        idealSelectedProduct (giantCandidatePerformedAuxiliarySplit S A B hAB aux).2 := by
  have h := giantCandidatePerformedAuxiliary_prod S (idealResidualFreeSlots (A ∪ B))
    (fun _ p => p.val) aux
  change giantTwoSidedPatternAuxiliaryProduct aux = giantTwoSidedPatternAuxiliaryProduct
    (giantCandidatePerformedAuxiliaryEquiv S (idealResidualFreeSlots (A ∪ B)) aux) at h
  rw [h, idealAuxiliarySelected_product, idealSelectedUnion_product _ A B hAB]
  rfl

theorem giantCandidatePerformedAuxiliarySplit_mass (A B : Finset (GiantCandidatePerformedBig S × Fin k))
    (hAB : Disjoint A B)
    (aux : GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S (idealResidualCopied (some (A,B))))) :
    giantTwoSidedPatternAuxiliaryMass aux =
      idealSelectedMass (idealResidualBands (giantCandidatePerformedBigBand S) A)
          (giantCandidatePerformedAuxiliarySplit S A B hAB aux).1 *
        idealSelectedMass (idealResidualBands (giantCandidatePerformedBigBand S) B)
          (giantCandidatePerformedAuxiliarySplit S A B hAB aux).2 := by
  have h := giantCandidatePerformedAuxiliary_prod S (idealResidualFreeSlots (A ∪ B))
    (fun g => markedHarmonicAtom (giantCandidateGroup x g.val)) aux
  change giantTwoSidedPatternAuxiliaryMass aux = giantTwoSidedPatternAuxiliaryMass
    (giantCandidatePerformedAuxiliaryEquiv S (idealResidualFreeSlots (A ∪ B)) aux) at h
  rw [h, idealAuxiliarySelected_mass, idealSelectedUnion_mass _ A B hAB]
  rfl

theorem giantCandidatePerformedAuxiliarySplit_expectation (A B : Finset (GiantCandidatePerformedBig S × Fin k))
    (hAB : Disjoint A B)
    (F : GiantTwoSidedPatternAuxiliary (fun g : S => giantCandidateGroup x g.val)
      (giantCandidatePerformedPattern S (idealResidualCopied (some (A,B)))) → ℂ) :
    (∑ aux, (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*F aux) =
      ∑ a : IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) A),
      ∑ b : IdealSelectedLabels (idealResidualBands (giantCandidatePerformedBigBand S) B),
        (idealSelectedMass (idealResidualBands (giantCandidatePerformedBigBand S) A) a:ℂ) *
        (idealSelectedMass (idealResidualBands (giantCandidatePerformedBigBand S) B) b:ℂ) *
        F ((giantCandidatePerformedAuxiliarySplit S A B hAB).symm (a,b)) := by
  let e := giantCandidatePerformedAuxiliarySplit S A B hAB
  rw [← e.symm.sum_comp (fun aux => (giantTwoSidedPatternAuxiliaryMass aux:ℂ)*F aux),
    Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  rw [giantCandidatePerformedAuxiliarySplit_mass S A B hAB, e.apply_symm_apply, Complex.ofReal_mul]

end
end ArtinMatthews
