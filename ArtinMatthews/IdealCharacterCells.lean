module

public import ArtinMatthews.IdealSelectedLabels
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The literal primitive-character kernel on retained logarithmic cells. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

def idealLogCell {P : I → Finset ℕ} (h : ℝ) (a : IdealSelectedLabels P) : ℤ :=
  ⌊Real.log (idealSelectedProduct a) / h⌋

def idealLogCellMass (P : I → Finset ℕ) (h : ℝ) (j : ℤ) : ℝ :=
  ∑ a : IdealSelectedLabels P, if idealLogCell h a = j then idealSelectedMass P a else 0

def idealCharacterReproducer (Q : ℕ) (d x : ℕ) : ℂ :=
  ∑ χ : IdealPrimitiveCharacters Q,
    star (idealPrimitiveCharacterValue χ d) * idealPrimitiveCharacterValue χ x

def idealCharacterCellKernel (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (d x : IdealSelectedLabels P) : ℂ :=
  if idealLogCell h d = idealLogCell h x ∧ ξ ≤ idealLogCellMass P h (idealLogCell h x) then
    ((idealLogCellMass P h (idealLogCell h x))⁻¹ : ℝ) *
      idealCharacterReproducer Q (idealSelectedProduct d) (idealSelectedProduct x)
  else 0

omit [DecidableEq I] in
theorem idealLogCell_bounds {P : I → Finset ℕ} {h : ℝ} (hh : 0 < h)
    (a : IdealSelectedLabels P) :
    (idealLogCell h a : ℝ) * h ≤ Real.log (idealSelectedProduct a) ∧
      Real.log (idealSelectedProduct a) < ((idealLogCell h a : ℝ) + 1) * h := by
  constructor
  · exact (le_div_iff₀ hh).mp (Int.floor_le _)
  · exact (div_lt_iff₀ hh).mp (Int.lt_floor_add_one _)

omit [DecidableEq I] in
theorem idealLogCell_localization {P : I → Finset ℕ} {h : ℝ} (hh : 0 < h)
    {d x : IdealSelectedLabels P} (heq : idealLogCell h d = idealLogCell h x) :
    |Real.log (idealSelectedProduct d) - Real.log (idealSelectedProduct x)| < h := by
  have hd := idealLogCell_bounds hh d
  have hx := idealLogCell_bounds hh x
  rw [heq] at hd
  rw [abs_lt]
  constructor <;> linarith

theorem idealLogCellMass_nonneg (P : I → Finset ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (h : ℝ) (j : ℤ) :
    0 ≤ idealLogCellMass P h j := by
  apply sum_nonneg
  intro a _
  split_ifs
  · exact idealSelectedMass_nonneg P hV a
  · exact le_rfl

theorem idealCharacterReproducer_norm_le (Q d x : ℕ) :
    ‖idealCharacterReproducer Q d x‖ ≤ (Q : ℝ)^2 := by
  calc
    _ ≤ ∑ χ : IdealPrimitiveCharacters Q,
        ‖star (idealPrimitiveCharacterValue χ d) * idealPrimitiveCharacterValue χ x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _χ : IdealPrimitiveCharacters Q, (1 : ℝ) := by
      apply sum_le_sum
      intro χ _
      rw [norm_mul, norm_star]
      calc
        _ ≤ 1 * 1 := mul_le_mul (idealPrimitiveCharacterValue_norm_le χ d)
          (idealPrimitiveCharacterValue_norm_le χ x) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul _
    _ = (Fintype.card (IdealPrimitiveCharacters Q) : ℝ) := by simp
    _ ≤ (Q : ℝ)^2 := by exact_mod_cast idealPrimitiveCharacters_card_le Q

theorem idealCharacterReproducer_star (Q d x : ℕ) :
    star (idealCharacterReproducer Q d x) = idealCharacterReproducer Q x d := by
  simp only [idealCharacterReproducer, star_sum, star_mul, star_star]

theorem idealCharacterCellKernel_discarded (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (d x : IdealSelectedLabels P)
    (hx : idealLogCellMass P h (idealLogCell h x) < ξ) :
    idealCharacterCellKernel P Q h ξ d x = 0 := by
  simp only [idealCharacterCellKernel, not_le.mpr hx, and_false, ite_false]

theorem idealCharacterCellKernel_support (P : I → Finset ℕ) (Q : ℕ) {h ξ : ℝ}
    (hh : 0 < h) (d x : IdealSelectedLabels P)
    (hk : idealCharacterCellKernel P Q h ξ d x ≠ 0) :
    |Real.log (idealSelectedProduct d) - Real.log (idealSelectedProduct x)| < h := by
  have heq : idealLogCell h d = idealLogCell h x := by
    by_contra hn
    exact hk (by simp only [idealCharacterCellKernel, hn, false_and, ite_false])
  exact idealLogCell_localization hh heq

theorem idealCharacterCellKernel_norm_le (P : I → Finset ℕ) (Q : ℕ) (h : ℝ)
    {ξ : ℝ} (hξ : 0 < ξ) (d x : IdealSelectedLabels P) :
    ‖idealCharacterCellKernel P Q h ξ d x‖ ≤ (Q : ℝ)^2 / ξ := by
  unfold idealCharacterCellKernel
  split_ifs with hr
  · have hm : 0 < idealLogCellMass P h (idealLogCell h x) := hξ.trans_le hr.2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
    calc
      _ ≤ (idealLogCellMass P h (idealLogCell h x))⁻¹ * (Q : ℝ)^2 :=
        mul_le_mul_of_nonneg_left (idealCharacterReproducer_norm_le _ _ _) (by positivity)
      _ ≤ ξ⁻¹ * (Q : ℝ)^2 :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hξ hr.2) (sq_nonneg _)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

end
end ArtinMatthews
