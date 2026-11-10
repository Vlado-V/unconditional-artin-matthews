module

public import ArtinMatthews.KummerSplittingDiscriminantBasis
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ArtinMatthews.KummerSplittingDiscriminantBound
public import ArtinMatthews.KummerSplittingDiscriminantHeight
public import ArtinMatthews.KummerSplittingDiscriminantNumeric
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual varying-prime Kummer field discriminant bounds. -/

namespace ArtinMatthews

/-- The actual splitting field has a polynomial-exponent discriminant bound
obtained from its constructed integral tower basis. -/
theorem primeKummerField_abs_discr_le {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {q : ℕ} (hq : q.Prime) (haq : a.natAbs ≤ q) :
    |(NumberField.discr (primeKummerField q a) : ℝ)| ≤ (q : ℝ) ^ (6 * q ^ 2) := by
  obtain ⟨b, hb, hheight⟩ := primeKummerField_integral_bounded_basis ha0 ha1 ham1 hq haq
  have hbound := KummerDiscriminant.abs_discr_le_integral_basis_height b hb
    (Nat.cast_nonneg q) hheight
  have hbound' : |(NumberField.discr (primeKummerField q a) : ℝ)| ≤
      (((q * (q - 1)).factorial : ℝ) * (q : ℝ) ^ (q * (q - 1))) ^ 2 := by
    simpa only [Fintype.card_fin] using hbound
  have hd : q * (q - 1) ≤ q ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_left q (Nat.sub_le q 1)
  exact hbound'.trans (KummerDiscriminant.factorial_mul_pow_sq_le hq.one_lt.le hd)

/-- In particular, the logarithmic discriminant grows at most as `6q² log q`.
The fixed integer base affects only the sufficient threshold `|a|≤q`. -/
theorem primeKummerField_log_discr_le {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {q : ℕ} (hq : q.Prime) (haq : a.natAbs ≤ q) :
    Real.log |(NumberField.discr (primeKummerField q a) : ℝ)| ≤
      6 * (q : ℝ) ^ 2 * Real.log q := by
  apply KummerDiscriminant.log_le_six_sq_log _ hq.pos
    (primeKummerField_abs_discr_le ha0 ha1 ham1 hq haq)
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero (primeKummerField q a))

/-- Every sufficiently large prime satisfies the actual discriminant estimate. -/
theorem eventually_log_discr_primeKummerField {a : ℤ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1) :
    ∀ᶠ q : ℕ in Filter.atTop, q.Prime →
      Real.log |(NumberField.discr (primeKummerField q a) : ℝ)| ≤
        6 * (q : ℝ) ^ 2 * Real.log q := by
  filter_upwards [Filter.eventually_ge_atTop a.natAbs] with q haq
  exact fun hq => primeKummerField_log_discr_le ha0 ha1 ham1 hq haq

end ArtinMatthews
