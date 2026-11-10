module

public import ArtinMatthews.GiantComparisonNumberedMarks
public import ArtinMatthews.IdealSelectedLabels
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

/-! A comparison test reads just the selected freed slots. Extend it to
natural lists by checking membership only at those coordinates. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J I : Type*} {k ell : ℕ} {P : J → Finset ℕ} {C : J → Finset (Fin k)}

def giantComparisonNumberedRead (lift : I → J)
    (slot : ∀ i, GiantTwoSidedPatternFreeSlots (C (lift i)) ell)
    (l : (j : J) → Fin (ell+(C j).card) → ℕ) (i : I) : ℕ :=
  l (lift i) (giantComparisonNumberedSlotEquiv (C (lift i)) ell (slot i))

def giantComparisonNumberedTest (lift : I → J)
    (slot : ∀ i, GiantTwoSidedPatternFreeSlots (C (lift i)) ell)
    (T : IdealSelectedLabels (fun i => P (lift i)) → ℂ)
    (l : (j : J) → Fin (ell+(C j).card) → ℕ) : ℂ :=
  if h : ∀ i, giantComparisonNumberedRead lift slot l i ∈ P (lift i) then
    T (fun i => ⟨giantComparisonNumberedRead lift slot l i,h i⟩)
  else 0

theorem giantComparisonNumberedTest_norm_le (lift : I → J)
    (slot : ∀ i, GiantTwoSidedPatternFreeSlots (C (lift i)) ell)
    (T : IdealSelectedLabels (fun i => P (lift i)) → ℂ) (hT : ∀ a, ‖T a‖ ≤ 1)
    (l : (j : J) → Fin (ell+(C j).card) → ℕ) :
    ‖giantComparisonNumberedTest lift slot T l‖ ≤ 1 := by
  unfold giantComparisonNumberedTest
  split_ifs with h
  · exact hT _
  · simp

theorem giantComparisonNumberedTest_congr (lift : I → J)
    (slot : ∀ i, GiantTwoSidedPatternFreeSlots (C (lift i)) ell)
    (T : IdealSelectedLabels (fun i => P (lift i)) → ℂ)
    {l l' : (j : J) → Fin (ell+(C j).card) → ℕ}
    (he : ∀ i, l (lift i) = l' (lift i)) :
    giantComparisonNumberedTest lift slot T l = giantComparisonNumberedTest lift slot T l' := by
  have hr : giantComparisonNumberedRead lift slot l =
      giantComparisonNumberedRead lift slot l' := by
    funext i
    unfold giantComparisonNumberedRead
    rw [he i]
  unfold giantComparisonNumberedTest
  rw [hr]

theorem giantComparisonNumberedTest_free (lift : I → J)
    (slot : ∀ i, GiantTwoSidedPatternFreeSlots (C (lift i)) ell)
    (T : IdealSelectedLabels (fun i => P (lift i)) → ℂ)
    (b : GiantComparisonFreeLabels P C ell) :
    giantComparisonNumberedTest lift slot T (giantComparisonNumberedFreeList P C ell b) =
      T (fun i => b (lift i) (slot i)) := by
  have hr : giantComparisonNumberedRead lift slot (giantComparisonNumberedFreeList P C ell b) =
      (fun i => (b (lift i) (slot i) : ℕ)) := by
    funext i
    exact giantComparisonNumberedFreeList_slot P C ell b _ _
  unfold giantComparisonNumberedTest
  rw [hr, dif_pos (fun i => (b (lift i) (slot i)).property)]

theorem sourceComparisonMarkWeight_conj [Fintype J] (P : J → Finset ℕ)
    (t : J → ℕ) (q : J → ℝ) (b : ((j : J) → Fin (t j) → ℕ) → ℂ) (n : ℕ) :
    conj (sourceComparisonMarkWeight P t q b n) =
      sourceComparisonMarkWeight P t q (fun l => conj (b l)) n := by
  simp only [sourceComparisonMarkWeight, map_div₀, map_mul, map_sum, Complex.conj_ofReal]

end
end ArtinMatthews
