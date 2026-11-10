module

public import ArtinMatthews.IdealLogCellPartition
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The character comparison on a retained logarithmic cell separates into
a bounded test of the free tuple and a bounded test of the endpoint marks.
The inverse cell mass is kept in the endpoint test. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

def giantComparisonCellFreeTest (P : I → Finset ℕ) (h : ℝ) (j : ℤ)
    {Q : ℕ} (χ : IdealPrimitiveCharacters Q) (d : IdealSelectedLabels P) : ℂ :=
  if idealLogCell h d = j then star (idealPrimitiveCharacterValue χ (idealSelectedProduct d)) else 0

def giantComparisonCellMarkTest (P : I → Finset ℕ) (h ξ : ℝ) (j : ℤ)
    {Q : ℕ} (χ : IdealPrimitiveCharacters Q) (a : IdealSelectedLabels P) : ℂ :=
  if idealLogCell h a = j ∧ ξ ≤ idealLogCellMass P h j then
    ((idealLogCellMass P h j)⁻¹ : ℝ) * idealPrimitiveCharacterValue χ (idealSelectedProduct a)
  else 0

omit [Fintype I] [DecidableEq I] in
theorem giantComparisonCellFreeTest_zero_of_ne (P : I → Finset ℕ) [Fintype I]
    (h : ℝ) (j : ℤ) {Q : ℕ} (χ : IdealPrimitiveCharacters Q) (d : IdealSelectedLabels P)
    (hd : idealLogCell h d ≠ j) : giantComparisonCellFreeTest P h j χ d = 0 := by
  simp [giantComparisonCellFreeTest, hd]

omit [DecidableEq I] in
theorem giantComparisonCellFreeTest_norm_le (P : I → Finset ℕ) (h : ℝ) (j : ℤ)
    {Q : ℕ} (χ : IdealPrimitiveCharacters Q) (d : IdealSelectedLabels P) :
    ‖giantComparisonCellFreeTest P h j χ d‖ ≤ 1 := by
  unfold giantComparisonCellFreeTest
  split_ifs
  · rw [norm_star]
    exact idealPrimitiveCharacterValue_norm_le χ _
  · simp

theorem giantComparisonCellMarkTest_norm_le (P : I → Finset ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (j : ℤ) {Q : ℕ} (χ : IdealPrimitiveCharacters Q) (a : IdealSelectedLabels P) :
    ‖giantComparisonCellMarkTest P h ξ j χ a‖ ≤ ξ⁻¹ := by
  unfold giantComparisonCellMarkTest
  split_ifs with ha
  · have hmass : 0 < idealLogCellMass P h j := hξ.trans_le ha.2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmass)]
    exact (mul_le_of_le_one_right (inv_nonneg.mpr hmass.le)
      (idealPrimitiveCharacterValue_norm_le χ _)).trans (inv_anti₀ hξ ha.2)
  · simpa only [norm_zero] using inv_nonneg.mpr hξ.le

theorem idealCharacterCellKernel_eq_comparison_sum (P : I → Finset ℕ)
    (Q : ℕ) (h ξ : ℝ) (d a : IdealSelectedLabels P) :
    idealCharacterCellKernel P Q h ξ d a =
      ∑ j ∈ idealLogCells P h, ∑ χ : IdealPrimitiveCharacters Q,
        giantComparisonCellFreeTest P h j χ d * giantComparisonCellMarkTest P h ξ j χ a := by
  rw [sum_eq_single_of_mem (idealLogCell h a) (idealLogCells_mem P h a) (fun j _ hj => by
    apply sum_eq_zero
    intro χ _
    simp [giantComparisonCellMarkTest, Ne.symm hj])]
  by_cases hd : idealLogCell h d = idealLogCell h a
  · by_cases ha : ξ ≤ idealLogCellMass P h (idealLogCell h a)
    · simp only [idealCharacterCellKernel, giantComparisonCellFreeTest, giantComparisonCellMarkTest,
        hd, ha, true_and, ite_true, idealCharacterReproducer, mul_sum]
      apply sum_congr rfl
      intro χ _
      ring
    · simp [idealCharacterCellKernel, giantComparisonCellMarkTest, ha]
  · simp [idealCharacterCellKernel, giantComparisonCellFreeTest, hd]

end
end ArtinMatthews
