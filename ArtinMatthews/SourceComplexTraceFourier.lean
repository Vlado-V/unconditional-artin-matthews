module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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
public import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped SchwartzMap FourierTransform RealInnerProductSpace
noncomputable section

/-- The additive measure for the complex trace character is twice planar volume. -/
def sourceComplexTraceMeasure : Measure ℂ := (2 : ENNReal) • volume

/-- The source's negative trace pairing is `exp(-4πi Re(xy))`. -/
def sourceComplexTraceFourier (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  ∫ x : ℂ, Real.fourierChar (-(2 * (x * y).re)) • f x ∂sourceComplexTraceMeasure

theorem source_complex_trace_inner (x y : ℂ) :
    inner ℝ x ((2 : ℝ) • star y) = 2 * (x * y).re := by
  rw [real_inner_smul_right, Complex.inner]
  congr 1
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem source_complex_trace_fourier_eq (f : ℂ → ℂ) (y : ℂ) :
    sourceComplexTraceFourier f y = 2 * 𝓕 f ((2 : ℝ) • star y) := by
  unfold sourceComplexTraceFourier sourceComplexTraceMeasure
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, Real.fourier_eq,
    source_complex_trace_inner]
  rfl

theorem source_complex_conjugate_integral (f : ℂ → ℂ) :
    (∫ z : ℂ, f (star z)) = ∫ z : ℂ, f z := by
  exact Complex.conjLIE.measurePreserving.integral_comp
    Complex.conjLIE.toHomeomorph.measurableEmbedding f

theorem source_complex_double_conjugate_integral (f : ℂ → ℂ) :
    (∫ z : ℂ, f ((2 : ℝ) • star z)) = (1 / 4 : ℂ) * ∫ z : ℂ, f z := by
  rw [source_complex_conjugate_integral (fun z => f ((2 : ℝ) • z)),
    Measure.integral_comp_smul volume f 2]
  norm_num [Complex.finrank_real_complex, smul_eq_mul]

theorem source_complex_double_conjugate_weight (a : ℝ) (z : ℂ) :
    (2 : ℝ) ^ a * ‖(2 : ℝ) • star z‖ ^ (-a) = ‖z‖ ^ (-a) := by
  rw [norm_smul]
  simp only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), norm_star]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg z), ← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  simp

theorem source_complex_double_conjugate_weighted_integral (f : ℂ → ℂ) (a : ℝ) :
    (∫ z : ℂ, f ((2 : ℝ) • star z) * (‖z‖ ^ (-a) : ℝ)) =
      ((2 : ℝ) ^ a : ℝ) / 4 * (∫ z : ℂ, f z * (‖z‖ ^ (-a) : ℝ)) := by
  calc
    _ = Complex.ofReal ((2 : ℝ) ^ a) *
        ∫ z : ℂ, f ((2 : ℝ) • star z) * (‖(2 : ℝ) • star z‖ ^ (-a) : ℝ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [mul_left_comm, ← Complex.ofReal_mul,
          source_complex_double_conjugate_weight]
    _ = _ := by
      rw [source_complex_double_conjugate_integral
        (fun z => f z * (‖z‖ ^ (-a) : ℝ))]
      ring

/-- Both the inner Fourier transform and the outer zeta integral use the source measure. -/
theorem source_complex_trace_zeta_eq (f : ℂ → ℂ) (a : ℝ) :
    (∫ z : ℂ, sourceComplexTraceFourier f z * (‖z‖ ^ (-a) : ℝ)
      ∂sourceComplexTraceMeasure) =
        Complex.ofReal ((2 : ℝ) ^ a) * (∫ z : ℂ, 𝓕 f z * (‖z‖ ^ (-a) : ℝ)) := by
  unfold sourceComplexTraceMeasure
  rw [integral_smul_measure]
  simp_rw [source_complex_trace_fourier_eq, mul_assoc]
  rw [integral_const_mul, source_complex_double_conjugate_weighted_integral]
  norm_num only [ENNReal.toReal_ofNat]
  change (2 : ℂ) * (2 * (_ / 4 * _)) = _
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
