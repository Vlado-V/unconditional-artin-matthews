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

/-! The conditional cell mass cancels in the literal harmonic row.
The bound is independent of the number or mass of retained cells. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem idealCharacterCellKernel_star (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (d x : IdealSelectedLabels P) :
    star (idealCharacterCellKernel P Q h ξ d x) = idealCharacterCellKernel P Q h ξ x d := by
  by_cases he : idealLogCell h d = idealLogCell h x
  · unfold idealCharacterCellKernel
    rw [he]
    simp only [true_and]
    split_ifs
    · rw [star_mul, idealCharacterReproducer_star]
      simp only [Complex.star_def, Complex.conj_ofReal]
      exact mul_comm _ _
    · exact star_zero _
  · have he' : idealLogCell h x ≠ idealLogCell h d := Ne.symm he
    simp only [idealCharacterCellKernel, he, he', false_and, ite_false, star_zero]

theorem idealCharacterCellKernel_norm_swap (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (d x : IdealSelectedLabels P) :
    ‖idealCharacterCellKernel P Q h ξ d x‖ = ‖idealCharacterCellKernel P Q h ξ x d‖ := by
  rw [← idealCharacterCellKernel_star, norm_star]

theorem idealCharacterCellKernel_row_le (P : I → Finset ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (Q : ℕ) (h : ℝ)
    {ξ : ℝ} (hξ : 0 < ξ) (x : IdealSelectedLabels P) :
    (∑ d, idealSelectedMass P d * ‖idealCharacterCellKernel P Q h ξ d x‖) ≤
      (Q : ℝ)^2 := by
  by_cases hr : ξ ≤ idealLogCellMass P h (idealLogCell h x)
  · have hm : 0 < idealLogCellMass P h (idealLogCell h x) := hξ.trans_le hr
    calc
      _ ≤ ∑ d, (if idealLogCell h d = idealLogCell h x then idealSelectedMass P d else 0) *
          ((idealLogCellMass P h (idealLogCell h x))⁻¹ * (Q : ℝ)^2) := by
        apply sum_le_sum
        intro d _
        by_cases hd : idealLogCell h d = idealLogCell h x
        · simp only [idealCharacterCellKernel, hd, hr, and_self, ite_true, norm_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (idealCharacterReproducer_norm_le _ _ _)
              (inv_nonneg.mpr hm.le)) (idealSelectedMass_nonneg P hV d)
        · simp only [idealCharacterCellKernel, hd, false_and, ite_false, norm_zero,
            mul_zero, zero_mul]
          exact le_rfl
      _ = idealLogCellMass P h (idealLogCell h x) *
          ((idealLogCellMass P h (idealLogCell h x))⁻¹ * (Q : ℝ)^2) := by
        rw [← sum_mul]
        rfl
      _ = (Q : ℝ)^2 := by rw [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
  · have hz (d : IdealSelectedLabels P) : idealCharacterCellKernel P Q h ξ d x = 0 := by
      simp only [idealCharacterCellKernel, hr, and_false, ite_false]
    simp only [hz, norm_zero, mul_zero, sum_const_zero]
    positivity

theorem idealCharacterCellKernel_column_le (P : I → Finset ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (Q : ℕ) (h : ℝ)
    {ξ : ℝ} (hξ : 0 < ξ) (d : IdealSelectedLabels P) :
    (∑ x, idealSelectedMass P x * ‖idealCharacterCellKernel P Q h ξ d x‖) ≤
      (Q : ℝ)^2 := by
  simpa only [idealCharacterCellKernel_norm_swap P Q h ξ d] using
    idealCharacterCellKernel_row_le P hV Q h hξ d

end
end ArtinMatthews
