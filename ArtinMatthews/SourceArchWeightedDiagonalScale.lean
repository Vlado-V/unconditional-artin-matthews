module

public import ArtinMatthews.SourceArchWeightedDiagonal
public import ArtinMatthews.SourceArchTraceComplexDilation
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

/-! Frequency dilation of the actual spherical Jacquet integral. -/

namespace ArtinMatthews.SourceArchJacquet
open ArtinMatthews.VaryingKummerAnalytic MeasureTheory Matrix
open scoped MatrixGroups
noncomputable section

/-- The exact spherical factor before applying the trace-measure Jacobian. -/
theorem sourceArchSphericalSection_bigCell_complex_dilation (s : ℂ) (b y : ℂˣ) (x : ℂ) :
    sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y) =
      (‖(b : ℂ)‖ : ℂ) ^ (2 * s + 1) *
        sourceArchSphericalSection s
          (sourcePGL2Weyl * sourcePGL2Upper ((b : ℂ) * x) * sourcePGL2Diagonal (b * y)) := by
  simp only [sourceArchSphericalSection_bigCell, Units.val_mul, norm_mul]
  let a := ‖(b : ℂ)‖
  let r := ‖(y : ℂ)‖
  let t := ‖x‖
  have ha : 0 < a := norm_pos_iff.mpr b.ne_zero
  have hr : 0 < r := norm_pos_iff.mpr y.ne_zero
  change ((r / (r ^ 2 + t ^ 2) : ℝ) : ℂ) ^ (2 * s + 1) =
    (a : ℂ) ^ (2 * s + 1) *
      (((a * r) / ((a * r) ^ 2 + (a * t) ^ 2) : ℝ) : ℂ) ^ (2 * s + 1)
  have hden : 0 < r ^ 2 + t ^ 2 := by positivity
  have hbase : r / (r ^ 2 + t ^ 2) = a * ((a * r) / ((a * r) ^ 2 + (a * t) ^ 2)) := by
    rw [show (a * r) ^ 2 + (a * t) ^ 2 = a ^ 2 * (r ^ 2 + t ^ 2) by ring]
    field_simp [ha.ne', hden.ne']
  have hpos : 0 ≤ (a * r) / ((a * r) ^ 2 + (a * t) ^ 2) := by positivity
  rw [hbase, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le hpos]

/-- The original negative frequency `-b` becomes `-1` at the dilated
height, with the precise positive-real complex power. -/
theorem sourceArchWeightedDiagonalProfile_frequency_scale (ψ : ℂ → ℂ) (s : ℂ) (b y : ℂˣ) :
    sourceArchWeightedDiagonalProfile ψ s (-(b : ℂ)) ‖(y : ℂ)‖ =
      (‖(b : ℂ)‖ : ℂ) ^ (2 * s - 1) *
        sourceArchWeightedDiagonalProfile ψ s (-1) ‖((b * y : ℂˣ) : ℂ)‖ := by
  let a := ‖(b : ℂ)‖
  let F : ℂ → ℂ := fun z => ψ ((-1 : ℂ) * z) *
    sourceArchSphericalSection s (sourcePGL2Weyl * sourcePGL2Upper z * sourcePGL2Diagonal (b * y))
  have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr b.ne_zero)
  have hpow : (a : ℂ) ^ (2 * s + 1) * (((a ^ 2)⁻¹ : ℝ) : ℂ) =
      (a : ℂ) ^ (2 * s - 1) := by
    rw [Complex.ofReal_inv, Complex.ofReal_pow, ← Complex.cpow_two, ← Complex.cpow_neg,
      ← Complex.cpow_add _ _ ha]
    congr 1
    ring
  rw [sourceArchWeightedDiagonalProfile_eq_integral ψ s (-(b : ℂ)) y,
    sourceArchWeightedDiagonalProfile_eq_integral ψ s (-1) (b * y)]
  change _ = (a : ℂ) ^ (2 * s - 1) * ∫ z : ℂ, F z ∂sourceComplexTraceMeasure
  calc
    _ = (a : ℂ) ^ (2 * s + 1) * ∫ x : ℂ, F ((b : ℂ) * x) ∂sourceComplexTraceMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [sourceArchSphericalSection_bigCell_complex_dilation s b y x]
      simp only [F, a, neg_mul]
      ring
    _ = _ := by
      rw [sourceArchTraceIntegral_mul_left F (b : ℂ) b.ne_zero, ← mul_assoc]
      exact congrArg (fun c : ℂ => c * ∫ z : ℂ, F z ∂sourceComplexTraceMeasure) hpow

end
end ArtinMatthews.SourceArchJacquet
