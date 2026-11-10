module

public import ArtinMatthews.SpectralABLWindows
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped BigOperators
noncomputable section

theorem spectralABLExceptionalWindow_den_ne_zero (A : ℕ) (z : ℂ)
    (hz : |z.im| < 2 * (A : ℝ)) : z ^ 2 + (2 * (A : ℂ)) ^ 2 ≠ 0 := by
  intro hzero
  have hr := congrArg Complex.re hzero
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hr
  have hp : 0 < (2 * (A : ℝ) - z.im) * (2 * (A : ℝ) + z.im) :=
    mul_pos (sub_pos.mpr (abs_lt.mp hz).2) (by linarith [(abs_lt.mp hz).1])
  nlinarith [sq_nonneg z.re]

theorem spectralABLExceptionalWindow_differentiableAt (a : ℝ) (A : ℕ) (z : ℂ)
    (hz : |z.im| < 2 * (A : ℝ)) :
    DifferentiableAt ℂ (spectralABLExceptionalWindow a A) z := by
  unfold spectralABLExceptionalWindow
  apply DifferentiableAt.mul
  · apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ (spectralABLExceptionalWindow_den_ne_zero A z hz)
  · fun_prop

theorem spectralABLExceptionalWindow_real_continuous (a : ℝ) {A : ℕ} (hA : 1 ≤ A) :
    Continuous (fun t : ℝ => spectralABLExceptionalWindow a A (t : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : |(t : ℂ).im| < 2 * (A : ℝ) := by
    have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
    simp only [Complex.ofReal_im, abs_zero]
    linarith
  exact (spectralABLExceptionalWindow_differentiableAt a A (t : ℂ) ht).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

theorem spectralABLRegularWindow_real_continuous (T Δ : ℝ) :
    Continuous (fun t : ℝ => spectralABLRegularWindow T Δ (t : ℂ)) :=
  (spectralABLRegularWindow_differentiable T Δ).continuous.comp Complex.continuous_ofReal

theorem spectralABLExceptionalPhase_eq_cpow {a : ℝ} (ha : 0 < a) (z : ℂ) :
    2 * Complex.cos (2 * z * (Real.log a : ℂ)) =
      (a : ℂ) ^ (2 * z * Complex.I) + (a : ℂ) ^ (-2 * z * Complex.I) := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [Complex.two_cos, Complex.cpow_def_of_ne_zero ha0, Complex.cpow_def_of_ne_zero ha0,
    ← Complex.ofReal_log ha.le]
  congr 1 <;> congr 1 <;> ring

end
end ArtinMatthews
