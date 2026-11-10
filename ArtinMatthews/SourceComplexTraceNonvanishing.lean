module

public import ArtinMatthews.SourceAnnularFourierTest
public import ArtinMatthews.SourceComplexTraceFourier
public import ArtinMatthews.SourceAnnularFourierNonvanishing
public import ArtinMatthews.SourceComplexZetaIntegrability
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped SchwartzMap FourierTransform
noncomputable section

theorem source_complex_double_conjugate_weighted_integrable (f : ℂ → ℂ) (a : ℝ)
    (hf : Integrable (fun z : ℂ => f z * (‖z‖ ^ (-a) : ℝ))) :
    Integrable (fun z : ℂ => f ((2 : ℝ) • star z) * (‖z‖ ^ (-a) : ℝ)) := by
  have h := Complex.conjLIE.measurePreserving.integrable_comp_of_integrable
    (hf.comp_smul (by norm_num : (2 : ℝ) ≠ 0))
  have hc := h.const_mul (Complex.ofReal ((2 : ℝ) ^ a))
  convert hc using 1
  funext z
  change f ((2 : ℝ) • star z) * ↑(‖z‖ ^ (-a)) =
    ↑((2 : ℝ) ^ a) * (f ((2 : ℝ) • star z) * ↑(‖(2 : ℝ) • star z‖ ^ (-a)))
  rw [mul_left_comm, ← Complex.ofReal_mul, source_complex_double_conjugate_weight]

theorem source_complex_trace_zeta_integrable (f : 𝓢(ℂ, ℂ))
    (a : ℝ) (ha : 0 ≤ a) (ha2 : a < 2) :
    Integrable (fun z : ℂ => sourceComplexTraceFourier f z * (‖z‖ ^ (-a) : ℝ))
      sourceComplexTraceMeasure := by
  have h := source_complex_double_conjugate_weighted_integrable (𝓕 (f : ℂ → ℂ)) a
    (source_complex_schwartz_fourier_weighted_integrable f a ha ha2)
  have hh := (h.const_mul (2 : ℂ)).smul_measure (by norm_num : (2 : ENNReal) ≠ ⊤)
  simpa only [sourceComplexTraceMeasure, source_complex_trace_fourier_eq, mul_assoc] using hh

theorem sourceAnnularSchwartzTest_trace_fourier_zero :
    sourceComplexTraceFourier sourceAnnularSchwartzTest 0 = 0 := by
  unfold sourceComplexTraceFourier sourceComplexTraceMeasure
  simp only [mul_zero, Complex.zero_re, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [integral_smul_measure, sourceAnnularSchwartzTest_integral, smul_zero]

theorem sourceAnnularSchwartzTest_trace_mellin_nonzero :
    (∫ z : ℂ, sourceComplexTraceFourier sourceAnnularSchwartzTest z *
      (‖z‖ ^ (-(5 / 3 : ℝ)) : ℝ) ∂sourceComplexTraceMeasure) ≠ 0 := by
  rw [source_complex_trace_zeta_eq]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))
  · exact sourceAnnularSchwartzTest_fourier_mellin_nonzero

theorem sourceAnnularSchwartzTest_trace_mellin_integrable :
    Integrable (fun z : ℂ => sourceComplexTraceFourier sourceAnnularSchwartzTest z *
      (‖z‖ ^ (-(5 / 3 : ℝ)) : ℝ)) sourceComplexTraceMeasure :=
  source_complex_trace_zeta_integrable sourceAnnularSchwartzTest (5 / 3)
    (by norm_num) (by norm_num)

/-- Normalized complex absolute value and multiplicative density at the source's 1/6. -/
theorem source_complex_one_sixth_density (z : ℂ) (hz : z ≠ 0) :
    (‖z‖ ^ 2) ^ (1 / 6 : ℝ) / ‖z‖ ^ 2 = ‖z‖ ^ (-(5 / 3 : ℝ)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul hn.le, ← Real.rpow_sub hn]
  norm_num

end
end ArtinMatthews.VaryingKummerAnalytic
