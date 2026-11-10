module

public import ArtinMatthews.IdealConditionalCharacterFrame
public import ArtinMatthews.IdealLogCellPartition
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The original retained log-cell kernel is a direct sum of its
conditional character frames under the original harmonic law. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

def idealCharacterCellApply (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (f : IdealSelectedLabels P → ℂ) (x : IdealSelectedLabels P) : ℂ :=
  ∑ d, (idealSelectedMass P d : ℂ) * idealCharacterCellKernel P Q h ξ d x * f d

theorem idealCharacterCellApply_retained (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (f : IdealSelectedLabels P → ℂ) (x : IdealSelectedLabels P)
    (hr : ξ ≤ idealLogCellMass P h (idealLogCell h x)) :
    idealCharacterCellApply P Q h ξ f x =
      idealConditionalCharacterFrame P Q h (idealLogCell h x) f x := by
  unfold idealCharacterCellApply idealConditionalCharacterFrame idealFrameApply idealFrameSynthesis
  simp only [idealFrameCoefficient, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  by_cases hd : idealLogCell h d = idealLogCell h x
  · rw [idealCharacterCellKernel, ite_eq_left ⟨hd, hr⟩, idealCharacterReproducer]
    simp only [mul_sum, sum_mul]
    apply sum_congr rfl
    intro χ _
    rw [idealCellConditionalMass, ite_eq_left hd, Complex.ofReal_div]
    push_cast
    ring
  · simp only [idealCharacterCellKernel, hd, false_and, ite_false, mul_zero, zero_mul,
      idealCellConditionalMass, Complex.ofReal_zero, sum_const_zero]

theorem idealCharacterCellApply_discarded (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (f : IdealSelectedLabels P → ℂ) (x : IdealSelectedLabels P)
    (hr : idealLogCellMass P h (idealLogCell h x) < ξ) :
    idealCharacterCellApply P Q h ξ f x = 0 := by
  unfold idealCharacterCellApply
  simp only [idealCharacterCellKernel_discarded P Q h ξ _ x hr, mul_zero, zero_mul, sum_const_zero]

theorem idealCellConditional_energy_scale (P : I → Finset ℕ) (h : ℝ) (j : ℤ)
    (hm : idealLogCellMass P h j ≠ 0) (f : IdealSelectedLabels P → ℂ) :
    idealLogCellMass P h j * idealFrameEnergy (idealCellConditionalMass P h j) f =
      ∑ x : IdealSelectedLabels P, if idealLogCell h x = j then
        idealSelectedMass P x * ‖f x‖^2 else 0 := by
  rw [idealFrameEnergy, mul_sum]
  apply sum_congr rfl
  intro x _
  unfold idealCellConditionalMass
  split_ifs
  · field_simp
  · simp only [zero_mul, mul_zero]

theorem idealCharacterCellApply_energy_le (P : I → Finset ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (Q : ℕ) (h : ℝ) {ξ B : ℝ}
    (hξ : 0 < ξ) (hB : 0 ≤ B)
    (hframe : ∀ j : ℤ, ξ ≤ idealLogCellMass P h j →
      ∀ f : IdealSelectedLabels P → ℂ,
        idealFrameEnergy (idealCellConditionalMass P h j)
            (idealConditionalCharacterFrame P Q h j f) ≤
          B * idealFrameEnergy (idealCellConditionalMass P h j) f)
    (f : IdealSelectedLabels P → ℂ) :
    idealFrameEnergy (idealSelectedMass P) (idealCharacterCellApply P Q h ξ f) ≤
      B * idealFrameEnergy (idealSelectedMass P) f := by
  have hcell (j : ℤ) :
      (∑ x : IdealSelectedLabels P, if idealLogCell h x = j then
        idealSelectedMass P x * ‖idealCharacterCellApply P Q h ξ f x‖^2 else 0) ≤
      B * ∑ x : IdealSelectedLabels P, if idealLogCell h x = j then
        idealSelectedMass P x * ‖f x‖^2 else 0 := by
    by_cases hr : ξ ≤ idealLogCellMass P h j
    · have hm : 0 < idealLogCellMass P h j := hξ.trans_le hr
      have hs := mul_le_mul_of_nonneg_left (hframe j hr f) hm.le
      rw [mul_left_comm (idealLogCellMass P h j) B,
        idealCellConditional_energy_scale P h j hm.ne' f,
        idealCellConditional_energy_scale P h j hm.ne'] at hs
      refine le_trans ?_ hs
      apply le_of_eq
      apply sum_congr rfl
      intro x _
      split_ifs with hx
      · rw [idealCharacterCellApply_retained P Q h ξ f x (by simpa only [hx] using hr), hx]
      · rfl
    · have hz : (∑ x : IdealSelectedLabels P, if idealLogCell h x = j then
          idealSelectedMass P x * ‖idealCharacterCellApply P Q h ξ f x‖^2 else 0) = 0 := by
        apply sum_eq_zero
        intro x _
        split_ifs with hx
        · rw [idealCharacterCellApply_discarded P Q h ξ f x (by simpa only [hx] using lt_of_not_ge hr)]
          simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
        · rfl
      rw [hz]
      apply mul_nonneg hB
      apply sum_nonneg
      intro x _
      split_ifs
      · exact mul_nonneg (idealSelectedMass_nonneg P hV x) (sq_nonneg _)
      · exact le_rfl
  calc
    _ = ∑ j ∈ idealLogCells P h, ∑ x : IdealSelectedLabels P,
        if idealLogCell h x = j then
          idealSelectedMass P x * ‖idealCharacterCellApply P Q h ξ f x‖^2 else 0 :=
      (idealLogCells_sum P h _).symm
    _ ≤ ∑ j ∈ idealLogCells P h, B * ∑ x : IdealSelectedLabels P,
        if idealLogCell h x = j then idealSelectedMass P x * ‖f x‖^2 else 0 :=
      sum_le_sum fun j _ => hcell j
    _ = _ := by rw [← mul_sum, idealLogCells_sum]; rfl

end
end ArtinMatthews
