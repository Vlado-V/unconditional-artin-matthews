module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd


set_option backward.privateInPublic true
@[expose] public section

namespace OAI
namespace Problem337

/-- The elementary square-root optimization of bad-point counting and
first-derivative cancellation, with explicit harmless constants. -/
theorem second_derivative_partition_sqrt_budget (A T lam : ℝ)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hlam : 0 < lam) (hlamone : lam ≤ 1) :
    (A * lam * T + 2 * Real.sqrt lam + 1) * (2 * Real.sqrt lam / lam + 1) +
      (A * lam * T + 2) * (2 / Real.sqrt lam + 1) ≤
        6 * A * T * Real.sqrt lam + 6 / Real.sqrt lam + 9 := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsq : (Real.sqrt lam)^2 = lam := Real.sq_sqrt hlam.le
  have hsone : Real.sqrt lam ≤ 1 := by
    nlinarith
  have hlams : lam ≤ Real.sqrt lam := by nlinarith
  have hat : 0 ≤ A * T := mul_nonneg hA hT
  have hprod : A * T * lam ≤ A * T * Real.sqrt lam := mul_le_mul_of_nonneg_left hlams hat
  have hratio : Real.sqrt lam / lam = 1 / Real.sqrt lam := by
    apply (div_eq_div_iff hlam.ne' hs.ne').mpr
    nlinarith
  rw [mul_div_assoc, hratio]
  have heq :
      (A * lam * T + 2 * Real.sqrt lam + 1) * (2 * (1 / Real.sqrt lam) + 1) +
        (A * lam * T + 2) * (2 / Real.sqrt lam + 1) =
      4 * A * T * Real.sqrt lam + 2 * A * T * lam +
        2 * Real.sqrt lam + 6 / Real.sqrt lam + 7 := by
    field_simp
    nlinarith [mul_nonneg hat (sq_nonneg (Real.sqrt lam))]
  convert heq.le.trans (show 4 * A * T * Real.sqrt lam + 2 * A * T * lam +
      2 * Real.sqrt lam + 6 / Real.sqrt lam + 7 ≤
      6 * A * T * Real.sqrt lam + 6 / Real.sqrt lam + 9 by nlinarith) using 1

end Problem337

end OAI
