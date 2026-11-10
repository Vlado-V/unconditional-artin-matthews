module

public import ArtinMatthews.SpectralKLRealKernel
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Spectral continuity and a literal compact-height K0 majorant for the
actual cosine K kernel. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralKLRealKernel_order_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => spectralKLRealKernel t x) := by
  unfold spectralKLRealKernel
  apply continuous_of_dominated (bound := fun u : ℝ => Real.exp (-x*Real.cosh u))
  · intro t
    exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-x*Real.cosh u)*Real.cos (t*u))).aestronglyMeasurable
  · intro t
    filter_upwards with u
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  · simpa only [zero_mul,Real.cos_zero,mul_one] using! spectralKLRealKernel_integrand_integrable 0 hx
  · filter_upwards with u
    fun_prop

theorem spectralKLRealKernel_zero_antitone {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    spectralKLRealKernel 0 x ≤ spectralKLRealKernel 0 a := by
  unfold spectralKLRealKernel
  apply integral_mono (spectralKLRealKernel_integrand_integrable 0 (ha.trans_le hax))
    (spectralKLRealKernel_integrand_integrable 0 ha)
  intro u
  simp only [zero_mul,Real.cos_zero,mul_one]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hax (Real.cosh_pos u).le
  linarith

theorem spectralKLRealKernel_norm_le_height (t : ℝ) {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    ‖spectralKLRealKernel t x‖ ≤ spectralKLRealKernel 0 a :=
  (spectralKLRealKernel_norm_le_zero t (ha.trans_le hax)).trans
    (spectralKLRealKernel_zero_antitone ha hax)

end ArtinMatthews
