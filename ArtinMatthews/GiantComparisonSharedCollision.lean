module

public import ArtinMatthews.GiantComparisonStripMass
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The comparison uses the actual copied complement of each pattern.
The good event excludes repeats, endpoint divisors and auxiliary labels. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} {P : J → Finset ℕ} {k : ℕ} {C : J → Finset (Fin k)}

def GiantComparisonSharedGood (aux : GiantTwoSidedPatternAuxiliary P C)
    (w w' : ℕ) (c : GiantComparisonSharedLabels P C) : Prop :=
  (∀ j, Function.Injective (c j)) ∧
  (∀ j (i : ↥(univ \ C j)), ¬ (c j i : ℕ) ∣ w ∧ ¬ (c j i : ℕ) ∣ w') ∧
  (∀ g j (i : ↥(C g)) (l : ↥(univ \ C j)), (aux g i : ℕ) ≠ (c j l : ℕ))

theorem GiantComparisonSharedGood.ne_free {aux : GiantTwoSidedPatternAuxiliary P C}
    {w w' : ℕ} {c : GiantComparisonSharedLabels P C}
    (hg : GiantComparisonSharedGood aux w w' c) {ell : ℕ}
    (b b' : GiantComparisonFreeLabels P C ell)
    (hb : ∀ j i, (b j i : ℕ) ∣ w) (hb' : ∀ j i, (b' j i : ℕ) ∣ w')
    (g j : J) (l : ↥(univ \ C g)) (i : GiantTwoSidedPatternFreeSlots (C j) ell) :
    (c g l : ℕ) ≠ (b j i : ℕ) ∧ (c g l : ℕ) ≠ (b' j i : ℕ) := by
  constructor
  · intro h
    apply (hg.2.1 g l).1
    rw [h]
    exact hb j i
  · intro h
    apply (hg.2.1 g l).2
    rw [h]
    exact hb' j i

variable [Fintype J] [DecidableEq J]

def giantComparisonSharedBadMass (aux : GiantTwoSidedPatternAuxiliary P C) (w w' : ℕ) : ℝ :=
  ∑ c : GiantComparisonSharedLabels P C,
    if GiantComparisonSharedGood aux w w' c then 0 else giantComparisonSharedMass c

theorem giantComparisonSharedBadMass_eq_event
    (aux : GiantTwoSidedPatternAuxiliary P C) (w w' : ℕ) :
    giantComparisonSharedBadMass aux w w' =
      markedEventMass giantComparisonSharedMass (fun c => ¬ GiantComparisonSharedGood aux w w' c) := by
  unfold giantComparisonSharedBadMass markedEventMass
  apply sum_congr rfl
  intro c _
  by_cases h : GiantComparisonSharedGood aux w w' c <;> simp [h]

end
end ArtinMatthews
