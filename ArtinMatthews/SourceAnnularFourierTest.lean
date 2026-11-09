module

public import ArtinMatthews.SourceAnnularZeroIntegral
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
open scoped ContDiff SchwartzMap
noncomputable section

def sourceAnnularComplexTest (z : ℂ) : ℂ := (sourceAnnularZeroTest z : ℂ)

theorem sourceAnnularComplexTest_smooth : ContDiff ℝ ∞ sourceAnnularComplexTest :=
  Complex.ofRealCLM.contDiff.comp sourceAnnularZeroTest_smooth

theorem sourceAnnularComplexTest_compact : HasCompactSupport sourceAnnularComplexTest :=
  sourceAnnularZeroTest_compact.comp_left Complex.ofReal_zero

theorem sourceAnnularComplexTest_support :
    tsupport sourceAnnularComplexTest = tsupport sourceAnnularZeroTest := by
  unfold tsupport
  congr 1
  ext z
  simp [Function.mem_support, sourceAnnularComplexTest]

def sourceAnnularSchwartzTest : 𝓢(ℂ, ℂ) :=
  sourceAnnularComplexTest_compact.toSchwartzMap sourceAnnularComplexTest_smooth

theorem sourceAnnularSchwartzTest_apply (z : ℂ) :
    sourceAnnularSchwartzTest z = (sourceAnnularZeroTest z : ℂ) := rfl

theorem sourceAnnularSchwartzTest_away_zero :
    tsupport sourceAnnularSchwartzTest ⊆ {z : ℂ | z ≠ 0} := by
  change tsupport sourceAnnularComplexTest ⊆ _
  rw [sourceAnnularComplexTest_support]
  exact sourceAnnularZeroTest_away_zero

theorem sourceAnnularSchwartzTest_integral :
    (∫ z : ℂ, sourceAnnularSchwartzTest z) = 0 := by
  simp_rw [sourceAnnularSchwartzTest_apply]
  rw [integral_complex_ofReal, sourceAnnularZeroTest_integral, Complex.ofReal_zero]

/-- Zero frequency vanishes for either sign and every real bilinear pairing. -/
theorem sourceAnnularSchwartzTest_fourier_zero (e : AddChar ℝ Circle)
    (L : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ) :
    VectorFourier.fourierIntegral e volume L sourceAnnularSchwartzTest 0 = 0 := by
  simpa [VectorFourier.fourierIntegral] using
    sourceAnnularSchwartzTest_integral

theorem sourceAnnularSchwartzTest_weighted_nonzero :
    (∫ z : ℂ, sourceAnnularSchwartzTest z * (‖z‖ ^ (-(1 / 3 : ℝ)) : ℝ)) ≠ 0 := by
  simp_rw [sourceAnnularSchwartzTest_apply, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  exact ne_of_lt sourceAnnularZeroTest_weighted_integral_neg

/-- The local normalized absolute value is the square of the complex norm. -/
theorem source_complex_five_sixths_density (z : ℂ) (hz : z ≠ 0) :
    (‖z‖ ^ 2) ^ (5 / 6 : ℝ) / ‖z‖ ^ 2 = ‖z‖ ^ (-(1 / 3 : ℝ)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul hn.le, ← Real.rpow_sub hn]
  norm_num

end
end ArtinMatthews.VaryingKummerAnalytic
