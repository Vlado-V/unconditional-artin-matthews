module

public import ArtinMatthews.SourceComplexTraceFourier
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
open scoped SchwartzMap FourierTransform BigOperators
noncomputable section

def sourceComplexTraceDecayConstant (f : 𝓢(ℂ, ℂ)) (n : ℕ) : ℝ :=
  2 * (2 ^ n * (Finset.Iic (n, 0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 f))

theorem sourceComplexTraceDecayConstant_nonneg (f : 𝓢(ℂ, ℂ)) (n : ℕ) :
    0 ≤ sourceComplexTraceDecayConstant f n := by
  unfold sourceComplexTraceDecayConstant
  positivity

theorem source_complex_trace_fourier_schwartz_eq (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    sourceComplexTraceFourier f z = 2 * (𝓕 f : 𝓢(ℂ, ℂ)) ((2 : ℝ) • star z) := by
  exact source_complex_trace_fourier_eq f z

theorem source_complex_trace_fourier_rapid_decay (f : 𝓢(ℂ, ℂ)) (n : ℕ) (z : ℂ) :
    (1 + ‖z‖) ^ n * ‖sourceComplexTraceFourier f z‖ ≤
      sourceComplexTraceDecayConstant f n := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (n, 0)) le_rfl le_rfl (𝓕 f : 𝓢(ℂ, ℂ)) ((2 : ℝ) • star z)
  simp only [norm_iteratedFDeriv_zero] at h
  have hz : 1 + ‖z‖ ≤ 1 + ‖(2 : ℝ) • star z‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      norm_star]
    linarith [norm_nonneg z]
  rw [source_complex_trace_fourier_schwartz_eq, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ = 2 * ((1 + ‖z‖) ^ n * ‖(𝓕 f : 𝓢(ℂ, ℂ)) ((2 : ℝ) • star z)‖) := by ring
    _ ≤ 2 * ((1 + ‖(2 : ℝ) • star z‖) ^ n *
        ‖(𝓕 f : 𝓢(ℂ, ℂ)) ((2 : ℝ) • star z)‖) := by
      gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

theorem source_complex_trace_fourier_decay (f : 𝓢(ℂ, ℂ)) (n : ℕ) (z : ℂ) :
    ‖sourceComplexTraceFourier f z‖ ≤
      sourceComplexTraceDecayConstant f n / (1 + ‖z‖) ^ n := by
  apply (le_div_iff₀ (pow_pos (by positivity) _)).mpr
  simpa only [mul_comm] using source_complex_trace_fourier_rapid_decay f n z

end
end ArtinMatthews.VaryingKummerAnalytic
