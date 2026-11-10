module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact powers in the passage from the weight-one functional equation to
its Bessel transform. Positive real bases avoid all branch ambiguities. -/

noncomputable section
namespace ArtinMatthews

/-- The scale of the dual normalized Bessel transform is `Q / P²`. -/
theorem voronoi_power_normalization (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) (s : ℂ) :
    (P : ℂ) ^ s * (Q : ℂ) ^ (1 - s) * (P : ℂ) ^ (-(1 - s)) =
      (P : ℂ) * ((Q / P ^ 2 : ℝ) : ℂ) ^ (1 - s) := by
  have hp : (P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hP.ne'
  have hpu : (P : ℂ) ^ (1 - s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hp)
  have he : (P : ℂ) ^ s * (P : ℂ) ^ (1 - s) = (P : ℂ) := by
    rw [← Complex.cpow_add _ _ hp]
    simp
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hQ.le (sq_nonneg P),
    show ((P ^ 2 : ℝ) : ℂ) = (P : ℂ) * (P : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg hP.le hP.le, Complex.cpow_neg]
  field_simp
  linear_combination (Q : ℂ) ^ (1 - s) * he

end ArtinMatthews
