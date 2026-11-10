module

public import ArtinMatthews.SourceComplexTraceFourier
public import ArtinMatthews.SourceComplexGaussianFourier
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The Gaussian integral with the actual complex trace pairing and
trace-self-dual measure. Both real dimensions are retained. -/
namespace ArtinMatthews.SourceArchJacquet

open MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped FourierTransform RealInnerProductSpace
noncomputable section

def sourceArchJacquetPhase (z : ℂ) : ℂ :=
  Real.fourierChar (-(2 * z.re))

theorem sourceArchJacquetPhase_norm (z : ℂ) : ‖sourceArchJacquetPhase z‖ = 1 := by
  exact Circle.norm_coe _

theorem sourceArchJacquetPhase_continuous : Continuous sourceArchJacquetPhase := by
  unfold sourceArchJacquetPhase
  fun_prop

theorem sourceArchGaussian_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℂ => (Real.exp (-t * ‖z‖ ^ 2) : ℂ)) sourceComplexTraceMeasure := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (t : ℂ)) (by simpa using ht) 0 0
  have hg : Integrable (fun z : ℂ => (Real.exp (-t * ‖z‖ ^ 2) : ℂ)) := by
    simpa only [zero_mul, add_zero, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow] using h
  exact hg.smul_measure (by norm_num)

theorem sourceArchGaussian_integral {t : ℝ} (ht : 0 < t) :
    (∫ z : ℂ, Real.exp (-t * ‖z‖ ^ 2) ∂sourceComplexTraceMeasure) = 2 * Real.pi / t := by
  unfold sourceComplexTraceMeasure
  rw [integral_smul_measure, GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  norm_num [Complex.finrank_real_complex, smul_eq_mul]
  ring

theorem sourceArchGaussianJacquet_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℂ => (Real.exp (-t * ‖z‖ ^ 2) : ℂ) * sourceArchJacquetPhase z)
      sourceComplexTraceMeasure := by
  apply (sourceArchGaussian_integrable ht).norm.mono'
    (((by fun_prop : Continuous (fun z : ℂ => (Real.exp (-t * ‖z‖ ^ 2) : ℂ))).mul
      sourceArchJacquetPhase_continuous).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun z => by
    change ‖(Real.exp (-t * ‖z‖ ^ 2) : ℂ) * sourceArchJacquetPhase z‖ ≤ _
    rw [norm_mul, sourceArchJacquetPhase_norm, mul_one]

theorem sourceArchGaussianJacquet_integral {t : ℝ} (ht : 0 < t) :
    (∫ z : ℂ, (Real.exp (-t * ‖z‖ ^ 2) : ℂ) * sourceArchJacquetPhase z ∂sourceComplexTraceMeasure) =
      ((2 * Real.pi / t * Real.exp (-(4 * Real.pi ^ 2) / t) : ℝ) : ℂ) := by
  have he : (∫ z : ℂ, (Real.exp (-t * ‖z‖ ^ 2) : ℂ) * sourceArchJacquetPhase z
      ∂sourceComplexTraceMeasure) =
      sourceComplexTraceFourier (fun z => (Real.exp (-t * ‖z‖ ^ 2) : ℂ)) 1 := by
    unfold sourceComplexTraceFourier sourceArchJacquetPhase
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by simp [Circle.smul_def, mul_comm]
  rw [he, source_complex_trace_fourier_eq, source_complex_gaussian_fourier t ht]
  have hn : ‖(2 : ℝ) • star (1 : ℂ)‖ ^ 2 = (4 : ℝ) := by norm_num [norm_smul]
  rw [hn, show -(Real.pi ^ 2 / t) * 4 = -(4 * Real.pi ^ 2) / t by ring]
  push_cast
  ring

end
end ArtinMatthews.SourceArchJacquet
