module

public import ArtinMatthews.GiantTwoSidedResiduePatternRows
public import ArtinMatthews.GiantSmallConditioningData
public import ArtinMatthews.GiantSmallConditioningBudget
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal small-state factor of a raw edge is the empty-auxiliary
residue kernel with the big copied product in its integer step. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {S : Type*} [Fintype S] [DecidableEq S] {PS : S → Finset ℕ} {k ell : ℕ}

private def smallEmptyAuxiliary (PS : S → Finset ℕ) (k : ℕ) :
    GiantTwoSidedPatternAuxiliary PS (fun _ => (∅ : Finset (Fin k))) :=
  fun _ i => False.elim (Finset.notMem_empty _ i.property)

private theorem small_auxiliary_sum {R : Type*} [AddCommMonoid R]
    (F : GiantTwoSidedPatternAuxiliary PS (fun _ => (∅ : Finset (Fin k))) → R) :
    (∑ a, F a) = F (smallEmptyAuxiliary PS k) := by
  classical
  apply Finset.sum_eq_single (smallEmptyAuxiliary PS k)
  · intro a _ ha
    have he : a = smallEmptyAuxiliary PS k := by
      funext j i
      exact False.elim (Finset.notMem_empty _ i.property)
    exact False.elim (ha he)
  · intro h
    exact False.elim (h (Finset.mem_univ _))

def giantSignedSmallEdgeWeight (κ : ℤ) (D : ℕ) (q : ℝ)
    (s t : GiantTwoSidedResidueState PS (k+ell)) : ℝ :=
  ‖giantTwoSidedResiduePatternCoefficient (κ * (D : ℤ)) q 0
    (fun _ _ _ => (1 : ℂ)) s t (smallEmptyAuxiliary PS k)‖

omit [DecidableEq S] in
theorem giantSignedSmallEdgeWeight_nonneg (κ : ℤ) (D : ℕ) (q : ℝ)
    (s t : GiantTwoSidedResidueState PS (k+ell)) :
    0 ≤ giantSignedSmallEdgeWeight κ D q s t := norm_nonneg _

omit [DecidableEq S] in
theorem giantSignedSmallEdgeWeight_eq
    (hP : ∀ j p, p ∈ PS j → p.Prime)
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (κ : ℤ) (D : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (s t : GiantTwoSidedResidueState PS (k+ell)) :
    giantSignedSmallEdgeWeight κ D q s t =
      if (∀ j : S, ∀ i : Fin k,
          t.val.2 j (Fin.castAdd ell i) = s.val.2 j (Fin.castAdd ell i)) ∧
        t.val.1 = giantTwoSidedResidueTranslate
          (κ * (((∏ j : S, ∏ i : Fin k, (s.val.2 j (Fin.castAdd ell i)).val) * D : ℕ) : ℤ))
            s.val.1 then
        giantSmallTailMass PS ell *
          giantTwoSidedResidueDamping PS (k+ell) q s.val.1 *
          giantTwoSidedResidueDamping PS (k+ell) q t.val.1
      else 0 := by
  unfold giantSignedSmallEdgeWeight
  rw [giantTwoSidedResiduePatternCoefficient_norm hP hV _ hq]
  have haux : giantTwoSidedPatternAuxiliaryProduct (smallEmptyAuxiliary PS k) = 1 := by
    simp [giantTwoSidedPatternAuxiliaryProduct]
  have hmass : giantTwoSidedPatternAuxiliaryMass (smallEmptyAuxiliary PS k) = 1 := by
    simp [giantTwoSidedPatternAuxiliaryMass]
  have hcond : GiantTwoSidedResiduePatternCondition (fun _ => (∅ : Finset (Fin k)))
      (κ * (D : ℤ)) s t (smallEmptyAuxiliary PS k) ↔
      (∀ j : S, ∀ i : Fin k,
          t.val.2 j (Fin.castAdd ell i) = s.val.2 j (Fin.castAdd ell i)) ∧
        t.val.1 = giantTwoSidedResidueTranslate
          (κ * (((∏ j : S, ∏ i : Fin k, (s.val.2 j (Fin.castAdd ell i)).val) * D : ℕ) : ℤ))
            s.val.1 := by
    have hprod : giantTwoSidedPatternCopiedProduct
        (fun _ => (∅ : Finset (Fin k))) s.val.2 =
        ∏ j : S, ∏ i : Fin k, (s.val.2 j (Fin.castAdd ell i)).val := by
      simp [giantTwoSidedPatternCopiedProduct]
    have hshift : (κ * (D : ℤ)) *
        ((giantTwoSidedPatternCopiedProduct (fun _ => (∅ : Finset (Fin k))) s.val.2 *
          giantTwoSidedPatternAuxiliaryProduct (smallEmptyAuxiliary PS k) : ℕ) : ℤ) =
        κ * (((∏ j : S, ∏ i : Fin k, (s.val.2 j (Fin.castAdd ell i)).val) * D : ℕ) : ℤ) := by
      rw [hprod, haux]
      push_cast
      ring
    constructor
    · intro h
      refine ⟨fun j i => h.1 j i (by simp), ?_⟩
      simpa only [hshift] using h.2.1
    · rintro ⟨hfirst, hres⟩
      refine ⟨fun j i _ => hfirst j i, ?_, ?_⟩
      · simpa only [hshift] using hres
      · intro g j i l
        exact False.elim (Finset.notMem_empty _ i.property)
  simp only [hcond, hmass, one_mul, norm_one, mul_one, ← giantSmallTailMass_eq_fresh]


variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedSmallEdgeWeight_row
    (hP : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (κ : ℤ) (D : ℕ) {q B : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hB : 0 ≤ B)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ B)
    (s : GiantTwoSidedResidueState PS (k+ell)) :
    (∑ t : GiantTwoSidedResidueState PS (k+ell), giantSignedSmallEdgeWeight κ D q s t) ≤
      B ^ Fintype.card S := by
  have h := giantTwoSidedResiduePatternAbsoluteRow_le hP hdis hV
    (C := fun _ => (∅ : Finset (Fin k))) (κ * (D : ℤ)) hq hq1 hB zero_le_one 0
    (fun _ _ _ => (1 : ℂ)) (fun _ _ _ => by simp)
    (fun j z => by simpa only [Finset.card_empty, Nat.add_zero] using hbudget j z) s
  simpa only [giantTwoSidedResiduePatternAbsoluteRow, small_auxiliary_sum, one_mul,
    giantSignedSmallEdgeWeight] using h

theorem giantSignedSmallEdgeWeight_column
    (hP : ∀ j p, p ∈ PS j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (PS i) (PS j)))
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (κ : ℤ) (D : ℕ) {q B : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hB : 0 ≤ B)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (PS j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ B)
    (t : GiantTwoSidedResidueState PS (k+ell)) :
    (∑ s : GiantTwoSidedResidueState PS (k+ell), giantSignedSmallEdgeWeight κ D q s t) ≤
      B ^ Fintype.card S := by
  have he := giantTwoSidedResiduePatternAbsoluteColumn_eq_reverse hP hV
    (C := fun _ => (∅ : Finset (Fin k))) (κ * (D : ℤ)) hq.le 0
    (fun _ _ _ => (1 : ℂ)) t
  have heq : (∑ s : GiantTwoSidedResidueState PS (k+ell),
      giantSignedSmallEdgeWeight κ D q s t) =
      ∑ s : GiantTwoSidedResidueState PS (k+ell), giantSignedSmallEdgeWeight (-κ) D q t s := by
    simpa only [giantTwoSidedResiduePatternAbsoluteColumn,
      giantTwoSidedResiduePatternAbsoluteRow, small_auxiliary_sum,
      giantSignedSmallEdgeWeight, neg_mul] using he
  rw [heq]
  exact giantSignedSmallEdgeWeight_row hP hdis hV (-κ) D hq hq1 hB hbudget t

end
end ArtinMatthews
