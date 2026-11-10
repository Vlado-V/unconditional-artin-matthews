module

public import ArtinMatthews.SourceArchUpperDerivative
public import ArtinMatthews.SourceArchPositivePowerBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceArch_row_upper_compare (c d x : ℂ) :
    ‖c‖^2 + ‖c*x+d‖^2 ≤ 2*(1+‖x‖^2)*(‖c‖^2+‖d‖^2) := by
  have hn : ‖c*x+d‖ ≤ ‖c‖*‖x‖+‖d‖ := by simpa only [norm_mul] using norm_add_le (c*x) d
  have hs : ‖c*x+d‖^2 ≤ 2*‖c‖^2*‖x‖^2+2*‖d‖^2 := by
    have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖c‖*‖x‖-‖d‖)]
  nlinarith [sq_nonneg ‖c‖, mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖d‖)]

def sourceArchUpperCompactConstant (R : ℝ) (z : ℂ) : ℝ :=
  2*(1+(R*‖z‖)^2)

theorem sourceArchUpperCompactConstant_one_le (R : ℝ) (z : ℂ) :
    1 ≤ sourceArchUpperCompactConstant R z := by
  unfold sourceArchUpperCompactConstant
  nlinarith [sq_nonneg (R*‖z‖)]

theorem sourceArchUpperDenominator_compare (g : GL (Fin 2) ℂ) (z : ℂ) {R t : ℝ}
    (ht : |t| ≤ R) :
    sourceArchUpperDenominator g z t ≤ sourceArchUpperCompactConstant R z * sourceArchBottomNorm g ∧
    sourceArchBottomNorm g ≤ sourceArchUpperCompactConstant R z * sourceArchUpperDenominator g z t := by
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  have hx : ‖(t : ℂ)*z‖ ≤ R*‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg z)
  have hC : 2*(1+‖(t : ℂ)*z‖^2) ≤ sourceArchUpperCompactConstant R z := by
    unfold sourceArchUpperCompactConstant
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hx 2]
  have hu := sourceArch_row_upper_compare (g 1 0) (g 1 1) ((t : ℂ)*z)
  have hl := sourceArch_row_upper_compare (g 1 0)
    (g 1 1+(t : ℂ)*(g 1 0*z)) (-((t : ℂ)*z))
  have he : g 1 0*((t : ℂ)*z)+g 1 1 = g 1 1+(t : ℂ)*(g 1 0*z) := by ring
  have he' : g 1 0*(-((t : ℂ)*z))+(g 1 1+(t : ℂ)*(g 1 0*z)) = g 1 1 := by ring
  rw [he] at hu
  rw [he', norm_neg] at hl
  constructor
  · exact hu.trans (mul_le_mul_of_nonneg_right hC (sourceArchBottomNorm_pos g).le)
  · exact hl.trans (mul_le_mul_of_nonneg_right hC (sourceArchUpperDenominator_pos g z t).le)

theorem sourceArchHeight_right_upper_compare (g : GL (Fin 2) ℂ) (z : ℂ) {R t : ℝ}
    (ht : |t| ≤ R) :
    sourceArchHeight (g*sourceKPUpperMatrix ℂ ((t : ℂ)*z)) ≤
        sourceArchUpperCompactConstant R z * sourceArchHeight g ∧
    sourceArchHeight g ≤ sourceArchUpperCompactConstant R z *
        sourceArchHeight (g*sourceKPUpperMatrix ℂ ((t : ℂ)*z)) := by
  obtain ⟨hu,hl⟩ := sourceArchUpperDenominator_compare g z ht
  have hd : 0 ≤ ‖(GeneralLinearGroup.det g : ℂ)‖ := norm_nonneg _
  rw [sourceArchHeight_right_upper, sourceArchHeight]
  constructor
  · rw [← mul_div_assoc, div_le_div_iff₀ (sourceArchUpperDenominator_pos g z t) (sourceArchBottomNorm_pos g)]
    nlinarith [mul_le_mul_of_nonneg_left hl hd]
  · rw [← mul_div_assoc, div_le_div_iff₀ (sourceArchBottomNorm_pos g) (sourceArchUpperDenominator_pos g z t)]
    nlinarith [mul_le_mul_of_nonneg_left hu hd]

theorem sourceArchUpperSection_compact_bound (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖sourceArchUpperSection s g z t‖ ≤
      (sourceArchUpperCompactConstant R z)^B * (sourceArchHeight g)^((2*s+1).re) := by
  rw [sourceArchUpperSection, sourceArchSphericalGL,
    Complex.norm_cpow_eq_rpow_re_of_pos (sourceArchHeight_pos _)]
  obtain ⟨hu,hl⟩ := sourceArchHeight_right_upper_compare g z ht
  exact sourceArch_positive_power_comparison (sourceArchHeight_pos _) (sourceArchHeight_pos g)
    (sourceArchUpperCompactConstant_one_le R z) hu hl hs

theorem sourceArchUpperSection_deriv_compact_bound (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖deriv (sourceArchUpperSection s g z) t‖ ≤
      (sourceArchUpperCompactConstant R z)^B * ‖2*s+1‖ * ‖z‖ *
        (sourceArchHeight g)^((2*s+1).re) := by
  calc
    _ ≤ ‖2*s+1‖*‖z‖*‖sourceArchUpperSection s g z t‖ := sourceArchUpperSection_deriv_bound s g z t
    _ ≤ ‖2*s+1‖*‖z‖*((sourceArchUpperCompactConstant R z)^B * (sourceArchHeight g)^((2*s+1).re)) :=
      mul_le_mul_of_nonneg_left (sourceArchUpperSection_compact_bound s g z ht hs) (by positivity)
    _ = _ := by ring

theorem sourceArchUpperSection_deriv_two_compact_bound (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ)
    {R t B : ℝ} (ht : |t| ≤ R) (hs : |(2*s+1).re| ≤ B) :
    ‖deriv (deriv (sourceArchUpperSection s g z)) t‖ ≤
      (sourceArchUpperCompactConstant R z)^B * (‖2*s+1‖^2+3*‖2*s+1‖) * ‖z‖^2 *
        (sourceArchHeight g)^((2*s+1).re) := by
  calc
    _ ≤ (‖2*s+1‖^2+3*‖2*s+1‖)*‖z‖^2*‖sourceArchUpperSection s g z t‖ :=
      sourceArchUpperSection_deriv_two_bound s g z t
    _ ≤ (‖2*s+1‖^2+3*‖2*s+1‖)*‖z‖^2*
        ((sourceArchUpperCompactConstant R z)^B * (sourceArchHeight g)^((2*s+1).re)) :=
      mul_le_mul_of_nonneg_left (sourceArchUpperSection_compact_bound s g z ht hs) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews.SourceArchJacquet
