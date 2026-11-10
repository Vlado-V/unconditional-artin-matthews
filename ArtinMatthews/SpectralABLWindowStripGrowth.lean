module

public import ArtinMatthews.SpectralABLWindows
public import ArtinMatthews.SpectralABLExceptionalStrip
public import ArtinMatthews.SpectralABLRegularStrip
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace ArtinMatthews
noncomputable section

theorem spectralABLRegularWindow_strip_polynomial (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3 / 4 →
      ‖spectralABLRegularWindow T Δ ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * (1 + t ^ 2) := by
  let E := Real.exp (1 / Δ ^ 2)
  refine ⟨(5 / 2) * E / T ^ 2, by dsimp [E]; positivity, ?_⟩
  intro t y hy
  have hy' : |y| ≤ (1 : ℝ) := hy.trans (by norm_num)
  have h := spectralABLRegularWindow_strip_bound hT hΔ t y hy'
  have hp : Real.exp (-(((t - T) / Δ) ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hm : Real.exp (-(((t + T) / Δ) ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  calc
    _ ≤ ((t ^ 2 + 5 / 4) / T ^ 2) * E * (1 + 1) :=
      h.trans (mul_le_mul_of_nonneg_left (add_le_add hp hm) (by positivity))
    _ ≤ _ := by
      have he : 0 ≤ E := Real.exp_nonneg _
      have halg : (t ^ 2 + 5 / 4) / T ^ 2 * E * (1 + 1) =
          (2 * E * (t ^ 2 + 5 / 4)) / T ^ 2 := by ring
      rw [halg, show 5 / 2 * E / T ^ 2 * (1 + t ^ 2) =
        (5 / 2 * E * (1 + t ^ 2)) / T ^ 2 by ring]
      apply div_le_div_of_nonneg_right _ (sq_nonneg T)
      nlinarith [mul_nonneg he (sq_nonneg t)]

theorem spectralABLExceptionalWindow_strip_polynomial (a : ℝ) (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3 / 4 →
      ‖spectralABLExceptionalWindow a A ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * (1 + t ^ 2) := by
  let C := 4 * Real.exp (4 * |Real.log a|) * ((2 * (A : ℝ) + 3) ^ 2) ^ (A + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t y hy
  have h := spectralABLExceptionalWindow_strip_bound a hA t y (hy.trans (by norm_num))
  have hp : (1 : ℝ) ≤ (1 + t ^ 2) ^ (A - 1) := one_le_pow₀ (by nlinarith [sq_nonneg t])
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ C / (1 + t ^ 2) ^ (A - 1) := by simpa only [C] using h
    _ ≤ C := div_le_self hC hp
    _ ≤ C * (1 + t ^ 2) := le_mul_of_one_le_right hC (by nlinarith [sq_nonneg t])

end
end ArtinMatthews
