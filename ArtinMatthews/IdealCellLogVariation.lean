module

public import ArtinMatthews.IdealLogPhase
public import ArtinMatthews.IdealCharacterCells
public import ArtinMatthews.IdealCharacterCellRows
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The true logarithmic support of the cell kernels controls the original
Mellin and additive slow phase, before either finite average is taken. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def idealCellLogVariation (P : A → Finset ℕ) (R : B → Finset ℕ)
    (Q r : ℕ) (h ξ ζ β : ℝ) (u : ℤ)
    (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) : ℂ :=
  ∑ d : IdealSelectedLabels P, ∑ e : IdealSelectedLabels R,
    (idealSelectedMass P d : ℂ) * idealCharacterCellKernel P Q h ξ d x *
      (idealSelectedMass R e : ℂ) * idealCharacterCellKernel R Q h ξ e y *
        (Real.fourierChar ((u : ℝ)*(idealSelectedProduct d : ℝ)*(idealSelectedProduct e : ℝ)/r) : ℂ) *
          (idealLogPhase ζ β (Real.log (idealSelectedProduct x) + Real.log (idealSelectedProduct y)) -
            idealLogPhase ζ β (Real.log (idealSelectedProduct d) + Real.log (idealSelectedProduct e)))

theorem idealCellLogVariation_bound (P : A → Finset ℕ) (R : B → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ i p, p ∈ R i → p.Prime)
    (hVP : ∀ i, 0 < bandReciprocalMass (P i)) (hVR : ∀ i, 0 < bandReciprocalMass (R i))
    (Q r : ℕ) {h ξ : ℝ} (hh : 0 < h) (hξ : 0 < ξ) (ζ β : ℝ) (u : ℤ)
    (x : IdealSelectedLabels P) (y : IdealSelectedLabels R) :
    ‖idealCellLogVariation P R Q r h ξ ζ β u x y‖ ≤ (Q : ℝ)^4 *
      (2*h*(|ζ| + 2*Real.pi * |β| * Real.exp (2*h)*(idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ))) := by
  let M : ℝ := Real.exp (2*h)*(idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ)
  let C : ℝ := 2*h*(|ζ| + 2*Real.pi * |β| * M)
  have hx : 0 < (idealSelectedProduct x : ℝ) := by exact_mod_cast idealSelectedProduct_pos hP x
  have hy : 0 < (idealSelectedProduct y : ℝ) := by exact_mod_cast idealSelectedProduct_pos hR y
  have hM : 0 < M := by dsimp [M]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlogM : Real.log M = 2*h + Real.log (idealSelectedProduct x) + Real.log (idealSelectedProduct y) := by
    dsimp only [M]
    rw [Real.log_mul (by positivity) hy.ne', Real.log_mul (Real.exp_pos _).ne' hx.ne', Real.log_exp]
  have hdiff (d : IdealSelectedLabels P) (e : IdealSelectedLabels R)
      (hd : idealCharacterCellKernel P Q h ξ d x ≠ 0)
      (he : idealCharacterCellKernel R Q h ξ e y ≠ 0) :
      ‖idealLogPhase ζ β (Real.log (idealSelectedProduct x) + Real.log (idealSelectedProduct y)) -
        idealLogPhase ζ β (Real.log (idealSelectedProduct d) + Real.log (idealSelectedProduct e))‖ ≤ C := by
    have ha := idealCharacterCellKernel_support P Q hh d x hd
    have hb := idealCharacterCellKernel_support R Q hh e y he
    have hsum : |(Real.log (idealSelectedProduct x) + Real.log (idealSelectedProduct y)) -
        (Real.log (idealSelectedProduct d) + Real.log (idealSelectedProduct e))| ≤ 2*h := by
      rw [abs_lt] at ha hb
      rw [abs_le]
      constructor <;> linarith
    have hs₁ : Real.log (idealSelectedProduct x) + Real.log (idealSelectedProduct y) ≤ Real.log M := by
      rw [hlogM]
      linarith
    have hs₂ : Real.log (idealSelectedProduct d) + Real.log (idealSelectedProduct e) ≤ Real.log M := by
      rw [hlogM]
      rw [abs_lt] at ha hb
      linarith
    exact (idealLogPhase_sub_le ζ β hM hs₁ hs₂).trans (by
      change (|ζ| + 2*Real.pi * |β| * M)*_ ≤ C
      dsimp only [C]
      have hcoef : 0 ≤ |ζ| + 2*Real.pi * |β| * M := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsum hcoef])
  have hp (d : IdealSelectedLabels P) : 0 ≤ idealSelectedMass P d := idealSelectedMass_nonneg P hVP d
  have hr (e : IdealSelectedLabels R) : 0 ≤ idealSelectedMass R e := idealSelectedMass_nonneg R hVR e
  calc
    _ ≤ ∑ d : IdealSelectedLabels P, ∑ e : IdealSelectedLabels R,
        idealSelectedMass P d * ‖idealCharacterCellKernel P Q h ξ d x‖ *
          (idealSelectedMass R e * ‖idealCharacterCellKernel R Q h ξ e y‖) * C := by
      unfold idealCellLogVariation
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro d _
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro e _
      by_cases hd : idealCharacterCellKernel P Q h ξ d x = 0
      · simp only [hd, mul_zero, zero_mul, norm_zero]
        exact le_rfl
      by_cases he : idealCharacterCellKernel R Q h ξ e y = 0
      · simp only [he, mul_zero, zero_mul, norm_zero]
        exact le_rfl
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp d),
        abs_of_nonneg (hr e), Circle.norm_coe, mul_one]
      have hw : 0 ≤ idealSelectedMass P d * ‖idealCharacterCellKernel P Q h ξ d x‖ *
          idealSelectedMass R e * ‖idealCharacterCellKernel R Q h ξ e y‖ :=
        mul_nonneg (mul_nonneg (mul_nonneg (hp d) (norm_nonneg _)) (hr e)) (norm_nonneg _)
      have hb := mul_le_mul_of_nonneg_left (hdiff d e hd he) hw
      convert hb using 1
      ring
    _ = ((∑ d : IdealSelectedLabels P, idealSelectedMass P d * ‖idealCharacterCellKernel P Q h ξ d x‖) *
        (∑ e : IdealSelectedLabels R, idealSelectedMass R e * ‖idealCharacterCellKernel R Q h ξ e y‖)) * C := by
      simp only [sum_mul, mul_sum]
      conv_rhs => rw [sum_comm]
    _ ≤ ((Q : ℝ)^2 * (Q : ℝ)^2) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply mul_le_mul (idealCharacterCellKernel_row_le P hVP Q h hξ x)
        (idealCharacterCellKernel_row_le R hVR Q h hξ y)
      · exact sum_nonneg fun e _ => mul_nonneg (hr e) (norm_nonneg _)
      · positivity
    _ = _ := by dsimp only [C, M]; ring

end
end ArtinMatthews
