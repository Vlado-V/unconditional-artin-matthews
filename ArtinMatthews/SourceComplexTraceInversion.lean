module

public import ArtinMatthews.SourceComplexTraceFourier
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
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

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace
noncomputable section

theorem source_complex_trace_fourier_twice (f : ℂ → ℂ) (x : ℂ) :
    sourceComplexTraceFourier (sourceComplexTraceFourier f) x = 𝓕 (𝓕 f) x := by
  unfold sourceComplexTraceFourier sourceComplexTraceMeasure
  rw [integral_smul_measure]
  change (2 : ℝ) • (∫ y : ℂ, Real.fourierChar (-(2 * (y * x).re)) •
    sourceComplexTraceFourier f y) = _
  simp_rw [source_complex_trace_fourier_eq, Circle.smul_def, smul_eq_mul,
    mul_left_comm _ (2 : ℂ)]
  rw [integral_const_mul]
  have heq : (fun y : ℂ => (Real.fourierChar (-(2 * (y * x).re)) : ℂ) *
      𝓕 f ((2 : ℝ) • star y)) =
      (fun y : ℂ => (Real.fourierChar (-inner ℝ ((2 : ℝ) • star y) x) : ℂ) *
        𝓕 f ((2 : ℝ) • star y)) := by
    funext y
    rw [real_inner_comm, source_complex_trace_inner]
    rw [mul_comm x y]
  rw [heq, source_complex_double_conjugate_integral
    (fun y => (Real.fourierChar (-inner ℝ y x) : ℂ) * 𝓕 f y)]
  rw [Real.fourier_eq]
  simp only [Circle.smul_def, smul_eq_mul]
  change (2 : ℂ) * (2 * ((1 / 4 : ℂ) * _)) = _
  ring

/-- This verifies that twice planar volume really is self-dual for the trace pairing. -/
theorem source_complex_trace_inversion (f : 𝓢(ℂ, ℂ)) (x : ℂ) :
    sourceComplexTraceFourier (sourceComplexTraceFourier f) x = f (-x) := by
  rw [source_complex_trace_fourier_twice]
  have hf : Integrable (𝓕 (f : ℂ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 f : 𝓢(ℂ, ℂ)).integrable
  have h := f.continuous.fourierInv_fourier_eq f.integrable hf
  have hx := congrFun h (-x)
  simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hx

end
end ArtinMatthews.VaryingKummerAnalytic
