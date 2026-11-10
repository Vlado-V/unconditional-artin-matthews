module

public import ArtinMatthews.IdealCharacterCells
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite partition by the selected product's logarithmic cells. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

def idealLogCells (P : I → Finset ℕ) (h : ℝ) : Finset ℤ :=
  univ.image (idealLogCell (P := P) h)

theorem idealLogCells_mem (P : I → Finset ℕ) (h : ℝ) (a : IdealSelectedLabels P) :
    idealLogCell h a ∈ idealLogCells P h :=
  mem_image.mpr ⟨a, mem_univ _, rfl⟩

theorem idealLogCells_sum {R : Type*} [AddCommMonoid R]
    (P : I → Finset ℕ) (h : ℝ) (f : IdealSelectedLabels P → R) :
    (∑ j ∈ idealLogCells P h, ∑ a : IdealSelectedLabels P,
      if idealLogCell h a = j then f a else 0) = ∑ a, f a := by
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [sum_ite_eq, idealLogCells_mem P h a, ite_true]

theorem idealLogCellMass_sum (P : I → Finset ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (h : ℝ) :
    (∑ j ∈ idealLogCells P h, idealLogCellMass P h j) = 1 := by
  change (∑ j ∈ idealLogCells P h, ∑ a : IdealSelectedLabels P,
    if idealLogCell h a = j then idealSelectedMass P a else 0) = 1
  rw [idealLogCells_sum, idealSelectedMass_sum P hV]

def idealDiscardedCellMass (P : I → Finset ℕ) (h ξ : ℝ) : ℝ :=
  ∑ a : IdealSelectedLabels P, if idealLogCellMass P h (idealLogCell h a) < ξ then
    idealSelectedMass P a else 0

theorem idealDiscardedCellMass_eq (P : I → Finset ℕ) (h ξ : ℝ) :
    idealDiscardedCellMass P h ξ =
      ∑ j ∈ idealLogCells P h, if idealLogCellMass P h j < ξ then idealLogCellMass P h j else 0 := by
  rw [idealDiscardedCellMass, ← idealLogCells_sum P h]
  apply sum_congr rfl
  intro j _
  by_cases hj : idealLogCellMass P h j < ξ
  · rw [ite_eq_left hj, idealLogCellMass]
    apply sum_congr rfl
    intro a _
    by_cases ha : idealLogCell h a = j
    · simp only [ha, hj, ite_true]
    · simp only [ha, ite_false]
  · rw [ite_eq_right hj]
    apply sum_eq_zero
    intro a _
    by_cases ha : idealLogCell h a = j
    · simp only [ha, hj, ite_true, ite_false]
    · simp only [ha, ite_false]

theorem idealDiscardedCellMass_le (P : I → Finset ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    idealDiscardedCellMass P h ξ ≤ (idealLogCells P h).card * ξ := by
  rw [idealDiscardedCellMass_eq]
  calc
    _ ≤ ∑ _j ∈ idealLogCells P h, ξ := by
      apply sum_le_sum
      intro j _
      split_ifs with hj
      · exact hj.le
      · exact hξ
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end
end ArtinMatthews
