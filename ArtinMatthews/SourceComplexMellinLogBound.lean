module

public import ArtinMatthews.SourceComplexMellinAbsolute
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

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped SchwartzMap
noncomputable section

theorem source_abs_log_mul_le_rpow_add (r e : ℝ) (hr : 0 < r) (he : 0 < e) :
    e * |Real.log r| ≤ r ^ e + r ^ (-e) := by
  have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hr e)
  have h2 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hr (-e))
  rw [Real.log_rpow hr] at h1 h2
  have h : e * |Real.log r| = |e * Real.log r| := by rw [abs_mul, abs_of_pos he]
  rw [h]
  apply abs_le.mpr
  constructor <;> linarith [Real.rpow_nonneg hr.le e, Real.rpow_nonneg hr.le (-e)]

theorem sourceComplexMellin_integrand_shift_norm (f : ℂ → ℂ) (s z : ℂ) (t : ℝ) (hz : z ≠ 0) :
    ‖f z * sourceComplexMellinWeight (s + (t : ℂ)) z‖ =
      ‖z‖ ^ (2 * t) * ‖f z * sourceComplexMellinWeight s z‖ := by
  simp only [norm_mul, sourceComplexMellinWeight_norm _ _ hz, Complex.add_re, Complex.ofReal_re]
  rw [show 2 * (s.re + t) - 2 = (2 * s.re - 2) + 2 * t by ring,
    Real.rpow_add (norm_pos_iff.mpr hz)]
  ring

def sourceComplexMellinDerivativeIntegrand (f : ℂ → ℂ) (s z : ℂ) : ℂ :=
  (2 * (Real.log ‖z‖ : ℂ)) * (f z * sourceComplexMellinWeight s z)

theorem sourceComplexMellin_derivative_norm_le (f : 𝓢(ℂ, ℂ)) (lo hi : ℝ) (s z : ℂ)
    (hlo : 0 < lo) (hl : lo ≤ s.re) (hh : s.re ≤ hi) (hz : z ≠ 0) :
    ‖sourceComplexMellinDerivativeIntegrand f s z‖ ≤
      (4 / lo) * sourceComplexMellinMajorant f (lo / 2) (hi + lo / 2) z := by
  have h2 : ‖(2 : ℂ) * (Real.log ‖z‖ : ℂ)‖ = 2 * |Real.log ‖z‖| := by
    rw [norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs]
  have hp := sourceComplexMellin_integrand_norm_le f (lo / 2) (hi + lo / 2)
    (s + ((lo / 2 : ℝ) : ℂ)) z (by simp; linarith) (by simp; linarith) hz
  have hm := sourceComplexMellin_integrand_norm_le f (lo / 2) (hi + lo / 2)
    (s + ((-(lo / 2) : ℝ) : ℂ)) z (by simp; linarith) (by simp; linarith) hz
  rw [sourceComplexMellin_integrand_shift_norm f s z _ hz,
    show (2 : ℝ) * (lo / 2) = lo by ring] at hp
  rw [sourceComplexMellin_integrand_shift_norm f s z _ hz,
    show (2 : ℝ) * (-(lo / 2)) = -lo by ring] at hm
  rw [sourceComplexMellinDerivativeIntegrand, norm_mul, h2]
  calc
    _ = (2 / lo) * (lo * |Real.log ‖z‖|) * ‖f z * sourceComplexMellinWeight s z‖ := by
      field_simp
    _ ≤ (2 / lo) * (‖z‖ ^ lo + ‖z‖ ^ (-lo)) * ‖f z * sourceComplexMellinWeight s z‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (source_abs_log_mul_le_rpow_add _ _ (norm_pos_iff.mpr hz) hlo) (by positivity)) (norm_nonneg _)
    _ = (2 / lo) * (‖z‖ ^ lo * ‖f z * sourceComplexMellinWeight s z‖ +
        ‖z‖ ^ (-lo) * ‖f z * sourceComplexMellinWeight s z‖) := by ring
    _ ≤ (2 / lo) * (sourceComplexMellinMajorant f (lo / 2) (hi + lo / 2) z +
        sourceComplexMellinMajorant f (lo / 2) (hi + lo / 2) z) :=
      mul_le_mul_of_nonneg_left (add_le_add hp hm) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews.VaryingKummerAnalytic
