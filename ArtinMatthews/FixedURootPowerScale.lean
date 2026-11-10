module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

/-! Absolute reciprocal-coordinate mass errors fit inside the actual root
power-saving scale. -/
namespace ArtinMatthews

/-- Both coordinate scales above `x^δ` dominate the bounded mass shift. -/
theorem fixedURoot_volume_power_ge_one {δ x U V : ℝ} (hδ : 0 < δ) (hx : 1 ≤ x)
    (hU : x^δ ≤ U) (hV : x^δ ≤ V) :
    1 ≤ U*V*x^(-δ/1000) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hUpos : 0 < U := (Real.rpow_pos_of_pos hxpos δ).trans_le hU
  calc
    1 ≤ x^(δ+δ-δ/1000) := Real.one_le_rpow hx (by linarith)
    _ = x^δ*x^δ*x^(-δ/1000) := by
      rw [show δ+δ-δ/1000 = (δ+δ)+(-δ/1000) by ring,
        Real.rpow_add hxpos,Real.rpow_add hxpos]
    _ ≤ U*V*x^(-δ/1000) := mul_le_mul_of_nonneg_right
      (mul_le_mul hU hV (Real.rpow_nonneg hxpos.le _) hUpos.le)
      (Real.rpow_nonneg hxpos.le _)

/-- The same absorption statement in the reciprocal `V≤U` regime. -/
theorem fixedURoot_reciprocal_error_scale_one_le {δ x U V : ℝ}
    (hδ : 0 < δ) (hx : 1 < x) (hV : x^δ ≤ V) (hVU : V ≤ U) :
    1 ≤ U*V*x^(-δ/1000) :=
  fixedURoot_volume_power_ge_one hδ hx.le (hV.trans hVU) hV

end ArtinMatthews
