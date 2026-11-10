module

public import ArtinMatthews.SpectralABLWindows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

theorem spectralGaussian_square_mul_le_one (s : ℝ) :
    s ^ 2 * Real.exp (-(s ^ 2)) ≤ 1 := by
  have h : s ^ 2 ≤ Real.exp (s ^ 2) := by linarith [Real.add_one_le_exp (s ^ 2)]
  calc
    _ ≤ Real.exp (s ^ 2) * Real.exp (-(s ^ 2)) :=
      mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add]; simp

theorem spectralGaussian_quadratic_bound (t m Δ : ℝ) (hΔ : 0 < Δ) :
    (t ^ 2 + 1 / 4) * Real.exp (-(((t - m) / Δ) ^ 2)) ≤
      2 * m ^ 2 + 1 / 4 + 2 * Δ ^ 2 := by
  let s := (t - m) / Δ
  have ht : t = m + Δ * s := by dsimp [s]; field_simp; ring
  have hs : t ^ 2 ≤ 2 * m ^ 2 + 2 * Δ ^ 2 * s ^ 2 := by
    rw [ht]
    nlinarith [sq_nonneg (m - Δ * s)]
  have he : Real.exp (-(s ^ 2)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg s))
  calc
    _ ≤ (2 * m ^ 2 + 1 / 4 + 2 * Δ ^ 2 * s ^ 2) * Real.exp (-(s ^ 2)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
    _ = (2 * m ^ 2 + 1 / 4) * Real.exp (-(s ^ 2)) +
        2 * Δ ^ 2 * (s ^ 2 * Real.exp (-(s ^ 2))) := by ring
    _ ≤ (2 * m ^ 2 + 1 / 4) * 1 + 2 * Δ ^ 2 * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left he (by positivity))
        (mul_le_mul_of_nonneg_left (spectralGaussian_square_mul_le_one s) (by positivity))
    _ = _ := by ring

def spectralABLRegularBound (T Δ : ℝ) : ℝ :=
  2 * (2 * T ^ 2 + 1 / 4 + 2 * Δ ^ 2) / T ^ 2

theorem spectralABLRegularWindowReal_le {T Δ : ℝ} (hT : 0 < T) (hΔ : 0 < Δ) (t : ℝ) :
    spectralABLRegularWindowReal T Δ t ≤ spectralABLRegularBound T Δ := by
  have hplus := spectralGaussian_quadratic_bound t T Δ hΔ
  have hminus := spectralGaussian_quadratic_bound t (-T) Δ hΔ
  simp only [sub_neg_eq_add, neg_sq] at hminus
  unfold spectralABLRegularWindowReal spectralABLRegularBound
  calc
    _ = ((t ^ 2 + 1 / 4) * Real.exp (-(((t - T) / Δ) ^ 2)) +
          (t ^ 2 + 1 / 4) * Real.exp (-(((t + T) / Δ) ^ 2))) / T ^ 2 := by ring
    _ ≤ ((2 * T ^ 2 + 1 / 4 + 2 * Δ ^ 2) +
          (2 * T ^ 2 + 1 / 4 + 2 * Δ ^ 2)) / T ^ 2 :=
      div_le_div_of_nonneg_right (add_le_add hplus hminus) (sq_pos_of_pos hT).le
    _ = _ := by ring

theorem spectralABLRegularWindow_norm_le {T Δ : ℝ} (hT : 0 < T) (hΔ : 0 < Δ) (t : ℝ) :
    ‖spectralABLRegularWindow T Δ (t : ℂ)‖ ≤ spectralABLRegularBound T Δ := by
  rw [spectralABLRegularWindow_real, Complex.norm_real,
    Real.norm_of_nonneg (spectralABLRegularWindowReal_nonneg T Δ t)]
  exact spectralABLRegularWindowReal_le hT hΔ t

end
end ArtinMatthews
