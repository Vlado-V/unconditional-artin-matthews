module

public import ArtinMatthews.SourceArchJacquetFubini
public import ArtinMatthews.SourceArchCubicLaplace
public import ArtinMatthews.SourceArchSphericalSection
public import ArtinMatthews.SourceThetaBesselMellin
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
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! The actual +1/6 spherical Jacquet integral and its exact source
theta normalization. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory OAI.CubicEisenstein
open ArtinMatthews.VaryingKummerAnalytic ArtinMatthews.SourceReflection
open scoped MatrixGroups
noncomputable section

theorem sourceArchJacquetIntegral_bessel {r : ℝ} (hr : 0 < r) :
    sourceArchJacquetIntegral r =
      (sourceArchJacquetConstant * r : ℝ) * schlafliBesselK (1 / 3 : ℂ) (4 * Real.pi * r) := by
  have h := sourceArchJacquetIntegral_laplace hr
  rw [sourceArchCubicLaplace_bessel hr] at h
  apply mul_left_cancel₀ (a := (Real.Gamma (4 / 3) : ℂ))
    (by exact_mod_cast (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).ne')
  calc
    _ = ((Real.Gamma (4 / 3) * sourceArchJacquetConstant * r : ℝ) : ℂ) *
        schlafliBesselK (1 / 3 : ℂ) (4 * Real.pi * r) := h
    _ = _ := by push_cast; ring

def sourceArchSphericalWhittaker (y : ℂˣ) : ℂ :=
  ∫ x : ℂ, sourceArchSphericalSection (1 / 6)
    (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y) *
      sourceArchJacquetPhase x ∂sourceComplexTraceMeasure

theorem sourceArchSphericalJacquet_kernel (y : ℂˣ) (x : ℂ) :
    sourceArchSphericalSection (1 / 6)
      (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y) *
        sourceArchJacquetPhase x = sourceArchJacquetKernel ‖(y : ℂ)‖ x := by
  have hr : 0 < ‖(y : ℂ)‖ := norm_pos_iff.mpr y.ne_zero
  have hd : 0 < ‖(y : ℂ)‖ ^ 2 + ‖x‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (sq_nonneg _)
  rw [sourceArchSphericalSection_bigCell]
  rw [show (2 : ℂ) * (1 / 6) + 1 = ((4 / 3 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (div_pos hr hd).le,
    Real.div_rpow hr.le hd.le, div_eq_mul_inv, ← Real.rpow_neg hd.le]
  rfl

theorem sourceArchSphericalWhittaker_integrable (y : ℂˣ) :
    Integrable (fun x : ℂ => sourceArchSphericalSection (1 / 6)
      (sourcePGL2Weyl * sourcePGL2Upper x * sourcePGL2Diagonal y) *
        sourceArchJacquetPhase x) sourceComplexTraceMeasure := by
  simp_rw [sourceArchSphericalJacquet_kernel]
  exact sourceArchJacquetKernel_integrable (norm_pos_iff.mpr y.ne_zero)

theorem sourceArchSphericalWhittaker_eq_bessel (y : ℂˣ) :
    sourceArchSphericalWhittaker y =
      (sourceArchJacquetConstant * ‖(y : ℂ)‖ : ℝ) *
        schlafliBesselK (1 / 3 : ℂ) (4 * Real.pi * ‖(y : ℂ)‖) := by
  unfold sourceArchSphericalWhittaker
  simp_rw [sourceArchSphericalJacquet_kernel]
  exact sourceArchJacquetIntegral_bessel (norm_pos_iff.mpr y.ne_zero)

theorem sourceArchSphericalWhittaker_sourceProfile (y : ℂˣ) :
    (sourceArchJacquetConstant : ℂ) * sourceThetaBesselProfile (4 * Real.pi) (‖(y : ℂ)‖ ^ 2) =
      (Real.sqrt (‖(y : ℂ)‖ ^ 2) : ℂ) * sourceArchSphericalWhittaker y := by
  rw [sourceArchSphericalWhittaker_eq_bessel, sourceThetaBesselProfile,
    Real.sqrt_sq (norm_nonneg _)]
  push_cast
  ring

theorem sourceThetaBesselProfile_eq_weightedWhittaker (y : ℂˣ) :
    sourceThetaBesselProfile (4 * Real.pi) (‖(y : ℂ)‖ ^ 2) =
      (Real.sqrt (‖(y : ℂ)‖ ^ 2) : ℂ) * sourceArchSphericalWhittaker y /
        (sourceArchJacquetConstant : ℂ) := by
  have hC : (sourceArchJacquetConstant : ℂ) ≠ 0 := by
    exact_mod_cast sourceArchJacquetConstant_ne_zero
  apply (eq_div_iff hC).mpr
  rw [mul_comm]
  exact sourceArchSphericalWhittaker_sourceProfile y

end
end ArtinMatthews.SourceArchJacquet
