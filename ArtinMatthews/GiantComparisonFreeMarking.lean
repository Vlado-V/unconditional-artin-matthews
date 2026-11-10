module

public import ArtinMatthews.GiantComparisonStripDamping
public import ArtinMatthews.GiantComparisonStripLabels
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

/-! The independent unshared marking is the actual ordered injection
into the active primes in each band, with its exact falling factorial. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantComparisonSlotEquiv {k : ℕ} (C : Finset (Fin k)) (ell : ℕ) :
    (↥(univ \ C) ⊕ GiantTwoSidedPatternFreeSlots C ell) ≃ Fin (k+ell) where
  toFun := Sum.elim (fun i => Fin.castAdd ell i.val) (giantTwoSidedPatternFreeSlot C ell)
  invFun := Fin.addCases (fun i =>
    if hi : i ∈ C then Sum.inr (Sum.inl ⟨i,hi⟩)
    else Sum.inl ⟨i,mem_sdiff.mpr ⟨mem_univ i,hi⟩⟩) (fun i => Sum.inr (Sum.inr i))
  left_inv := by
    rintro (i | i | i)
    · simp [(mem_sdiff.mp i.property).2]
    · simp [giantTwoSidedPatternFreeSlot, i.property]
    · simp [giantTwoSidedPatternFreeSlot]
  right_inv l := by
    refine Fin.addCases (m:=k) (n:=ell) ?_ ?_ l
    · intro i
      by_cases hi : i ∈ C <;> simp [giantTwoSidedPatternFreeSlot, hi]
    · intro i
      simp [giantTwoSidedPatternFreeSlot]

variable {J : Type*} {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)}

theorem giantComparisonJoinLabels_injective_iff (c : GiantComparisonSharedLabels P C)
    (b : GiantComparisonFreeLabels P C ell) (j : J) :
    Function.Injective (giantComparisonJoinLabels c b j) ↔
      Function.Injective (c j) ∧ Function.Injective (b j) ∧ ∀ i l, c j i ≠ b j l := by
  let e := giantComparisonSlotEquiv (C j) ell
  have he : (giantComparisonJoinLabels c b j) ∘ e = Sum.elim (c j) (b j) := by
    funext u
    cases u with
    | inl i => exact giantComparisonJoinLabels_shared c b j i
    | inr i => exact giantComparisonJoinLabels_free c b j i
  constructor
  · intro h
    have hsum := h.comp e.injective
    rw [he] at hsum
    exact Sum.elim_injective.mp hsum
  · intro h
    have hsum := Sum.elim_injective.mpr h
    rw [← he] at hsum
    intro i l hil
    apply e.symm.injective
    apply hsum
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hil

abbrev GiantComparisonFreeMarking (P : J → Finset ℕ) (C : J → Finset (Fin k))
    (ell w : ℕ) :=
  {b : GiantComparisonFreeLabels P C ell //
    (∀ j, Function.Injective (b j)) ∧ ∀ j i, (b j i : ℕ) ∣ w}

def giantComparisonFreeMarkingEquiv (P : J → Finset ℕ) (C : J → Finset (Fin k)) (ell w : ℕ) :
    GiantComparisonFreeMarking P C ell w ≃
      ((j : J) → GiantTwoSidedPatternFreeSlots (C j) ell ↪ ↥(activeDivisors (P j) w)) where
  toFun b j := ⟨fun i => ⟨(b.val j i:ℕ), mem_filter.mpr ⟨(b.val j i).property,b.property.2 j i⟩⟩,
    fun _ _ h => b.property.1 j (Subtype.ext (congrArg (fun p : ↥(activeDivisors (P j) w) => p.val) h))⟩
  invFun b := ⟨fun j i => ⟨(b j i:ℕ),(mem_filter.mp (b j i).property).1⟩,
    fun j _ _ h => (b j).injective (Subtype.ext (congrArg (fun p : ↥(P j) => p.val) h)),
    fun j i => (mem_filter.mp (b j i).property).2⟩
  left_inv b := by
    apply Subtype.ext
    funext j i
    rfl
  right_inv b := by
    funext j
    apply Function.Embedding.ext
    intro i
    rfl

theorem giantComparisonFreeMarking_card [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (C : J → Finset (Fin k)) (ell w : ℕ) :
    Fintype.card (GiantComparisonFreeMarking P C ell w) =
      ∏ j, (bandCount (P j) w).descFactorial (ell+(C j).card) := by
  rw [Fintype.card_congr (giantComparisonFreeMarkingEquiv P C ell w), Fintype.card_pi]
  simp only [Fintype.card_embedding_eq, Fintype.card_sum, Fintype.card_coe, Fintype.card_fin,
    bandCount, Nat.add_comm]

def giantComparisonOrderedFreeWeight [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (C : J → Finset (Fin k)) (ell : ℕ) (q : ℝ) (w : ℕ) : ℝ :=
  (Fintype.card (GiantComparisonFreeMarking P C ell w) : ℝ)*
    giantTwoSidedPatternFreshMass P C ell*giantComparisonQuotientDamping P C ell q w

theorem giantComparisonOrderedFreeWeight_eq [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (C : J → Finset (Fin k)) (ell : ℕ) (q : ℝ) (w : ℕ) :
    giantComparisonOrderedFreeWeight P C ell q w =
      ∏ j, ((bandCount (P j) w).descFactorial (ell+(C j).card):ℝ) /
        (bandReciprocalMass (P j))^(ell+(C j).card) * q^(bandCount (P j) w-(ell+(C j).card)) := by
  unfold giantComparisonOrderedFreeWeight
  rw [giantComparisonFreeMarking_card]
  by_cases h : ∀ j, ell+(C j).card ≤ bandCount (P j) w
  · rw [Nat.cast_prod, giantTwoSidedPatternFreshMass, giantComparisonQuotientDamping,
      giantCandidateBandCount_union P hdis w, ← sum_tsub_distrib univ (fun j _ => h j),
      ← prod_pow_eq_pow_sum]
    simp only [prod_mul_distrib, div_eq_mul_inv, inv_pow]
  · push Not at h
    obtain ⟨j,hj⟩ := h
    have hz := Nat.descFactorial_of_lt hj
    rw [prod_eq_zero (mem_univ j) hz, Nat.cast_zero, zero_mul, zero_mul]
    exact (prod_eq_zero (mem_univ j) (by rw [hz, Nat.cast_zero, zero_div, zero_mul])).symm

end
end ArtinMatthews
