module

public import ArtinMatthews.SpectralKLCoshIntegrability
public import ArtinMatthews.SpectralABLWindowFirstMoments
public import ArtinMatthews.SpectralABLWindowPositivity


set_option backward.privateInPublic true
@[expose] public section

/-! Actual source windows are integrable in the KL spectral measure
at the parameters needed for the bare diagonal trace. -/

noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

theorem spectralABLRegularCorrected_integrable (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) :
    Integrable (fun t : ℝ => spectralABLRegularCorrected T Δ (t : ℂ)) spectralKLSpectralMeasure := by
  apply spectralKLCosh_integrable _ (spectralABLRegularWindowReal T Δ)
  · have he (t : ℝ) : spectralABLRegularCorrected T Δ (t : ℂ) =
        (spectralABLRegularWindowReal T Δ t : ℂ)/(Real.cosh (Real.pi*t) : ℂ) := by
      rw [spectralABLRegularCorrected_real,spectralABLRegularWindow_real]
    simp_rw [he]
    unfold spectralABLRegularWindowReal
    fun_prop
  · exact fun t _ => spectralABLRegularWindowReal_nonneg T Δ t
  · exact spectralABLRegularWindowReal_first_moment_integrable hT hΔ
  · exact fun t _ => (spectralABLRegularCorrected_norm_real T Δ t).le

theorem spectralABLExceptionalCorrected_integrable (a : ℝ) (A : ℕ) (hA : 3 ≤ A) :
    Integrable (fun t : ℝ => spectralABLExceptionalCorrected a A (t : ℂ)) spectralKLSpectralMeasure := by
  apply spectralKLCosh_integrable _ (spectralABLExceptionalWindowReal a A)
  · have he (t : ℝ) : spectralABLExceptionalCorrected a A (t : ℂ) =
        (spectralABLExceptionalWindowReal a A t : ℂ)/(Real.cosh (Real.pi*t) : ℂ) := by
      rw [spectralABLExceptionalCorrected_real,spectralABLExceptionalWindow_real]
    simp_rw [he]
    unfold spectralABLExceptionalWindowReal
    fun_prop
  · exact fun t _ => spectralABLExceptionalWindowReal_nonneg a A t
  · exact spectralABLExceptionalWindowReal_first_moment_integrable a hA
  · exact fun t _ => (spectralABLExceptionalCorrected_norm_real a A t).le

end ArtinMatthews
