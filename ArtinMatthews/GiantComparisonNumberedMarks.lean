module

public import ArtinMatthews.GiantComparisonFreeMarking
public import ArtinMatthews.SourceComparisonMarkWeight
public import ArtinMatthews.GiantCandidateAllocationWeights
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Number the original copied and padding slots without changing the
ordered distinct divisor lists or their reciprocal mass and damping. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantComparisonNumberedSlotEquiv {k : ℕ} (C : Finset (Fin k)) (ell : ℕ) :
    GiantTwoSidedPatternFreeSlots C ell ≃ Fin (ell+C.card) :=
  (Equiv.sumCongr (C.orderIsoOfFin rfl).toEquiv.symm (Equiv.refl (Fin ell))).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_comm C.card ell)))

variable {J : Type*} {k : ℕ}

def giantComparisonNumberedFreeList (P : J → Finset ℕ) (C : J → Finset (Fin k)) (ell : ℕ)
    (b : GiantComparisonFreeLabels P C ell) (j : J) (i : Fin (ell+(C j).card)) : ℕ :=
  b j ((giantComparisonNumberedSlotEquiv (C j) ell).symm i)

@[simp] theorem giantComparisonNumberedFreeList_slot (P : J → Finset ℕ)
    (C : J → Finset (Fin k)) (ell : ℕ) (b : GiantComparisonFreeLabels P C ell)
    (j : J) (i : GiantTwoSidedPatternFreeSlots (C j) ell) :
    giantComparisonNumberedFreeList P C ell b j (giantComparisonNumberedSlotEquiv (C j) ell i) =
      (b j i : ℕ) := by
  simp [giantComparisonNumberedFreeList]

variable [Fintype J] [DecidableEq J]

def giantComparisonFreeMarkingNumberedEquiv (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell w : ℕ) :
    GiantComparisonFreeMarking P C ell w ≃
      ↥(sourceComparisonMarkChoices (fun j => activeDivisors (P j) w) (fun j => ell+(C j).card)) where
  toFun b := ⟨giantComparisonNumberedFreeList P C ell b.val,
    (mem_sourceComparisonMarkChoices _ _ _).mpr
      ⟨fun j i => mem_filter.mpr
        ⟨(b.val j _).property,b.property.2 j _⟩,
        fun j i l h => (giantComparisonNumberedSlotEquiv (C j) ell).symm.injective
          (b.property.1 j (Subtype.ext h))⟩⟩
  invFun z :=
    let hz := (mem_sourceComparisonMarkChoices _ _ _).mp z.property
    ⟨fun j i => ⟨z.val j (giantComparisonNumberedSlotEquiv (C j) ell i),
      (mem_filter.mp (hz.1 j _)).1⟩,
      fun j i l h => (giantComparisonNumberedSlotEquiv (C j) ell).injective
        (hz.2 j (congrArg Subtype.val h)),
      fun j i => (mem_filter.mp (hz.1 j (giantComparisonNumberedSlotEquiv (C j) ell i))).2⟩
  left_inv z := by
    apply Subtype.ext
    funext j i
    apply Subtype.ext
    exact giantComparisonNumberedFreeList_slot P C ell z.val j i
  right_inv z := by
    apply Subtype.ext
    funext j i
    change z.val j (giantComparisonNumberedSlotEquiv (C j) ell
      ((giantComparisonNumberedSlotEquiv (C j) ell).symm i)) = z.val j i
    rw [Equiv.apply_symm_apply]

theorem giantComparisonNumberedFreeList_sum (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell w : ℕ) (b : ((j : J) → Fin (ell+(C j).card) → ℕ) → ℂ) :
    (∑ l ∈ sourceComparisonMarkChoices (fun j => activeDivisors (P j) w)
      (fun j => ell+(C j).card), b l) =
      ∑ z : GiantComparisonFreeMarking P C ell w, b (giantComparisonNumberedFreeList P C ell z.val) := by
  rw [← sum_coe_sort]
  exact (Equiv.sum_comp (giantComparisonFreeMarkingNumberedEquiv P C ell w)
    (fun l => b l.val)).symm

theorem sourceComparisonMarkWeight_eq_freeMarking_sum (P : J → Finset ℕ)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (C : J → Finset (Fin k))
    (ell : ℕ) (q : ℝ) (b : ((j : J) → Fin (ell+(C j).card) → ℕ) → ℂ) (w : ℕ) :
    sourceComparisonMarkWeight P (fun j => ell+(C j).card) (fun _ => q) b w =
      ((giantTwoSidedPatternFreshMass P C ell *
        giantComparisonQuotientDamping P C ell q w : ℝ) : ℂ) *
        ∑ z : GiantComparisonFreeMarking P C ell w, b (giantComparisonNumberedFreeList P C ell z.val) := by
  rw [sourceComparisonMarkWeight, giantComparisonNumberedFreeList_sum]
  by_cases h : ∀ j, ell+(C j).card ≤ bandCount (P j) w
  · have hd : sourceComparisonMarkHitDamping P (fun j => ell+(C j).card) (fun _ => q) w =
        giantComparisonQuotientDamping P C ell q w := by
      rw [sourceComparisonMarkHitDamping, giantComparisonQuotientDamping,
        giantCandidateBandCount_union P hdis w, ← sum_tsub_distrib univ (fun j _ => h j),
        ← prod_pow_eq_pow_sum]
    have hm : (sourceComparisonMarkMass P (fun j => ell+(C j).card))⁻¹ =
        giantTwoSidedPatternFreshMass P C ell := by
      simp only [sourceComparisonMarkMass, giantTwoSidedPatternFreshMass, prod_inv_distrib, inv_pow]
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, hm, hd, Complex.ofReal_mul]
    ring
  · push Not at h
    obtain ⟨j,hj⟩ := h
    have hc : Fintype.card (GiantComparisonFreeMarking P C ell w) = 0 := by
      rw [giantComparisonFreeMarking_card]
      exact prod_eq_zero (mem_univ j) (Nat.descFactorial_of_lt hj)
    letI := Fintype.card_eq_zero_iff.mp hc
    simp

end
end ArtinMatthews
