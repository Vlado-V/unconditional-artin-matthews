module

public import ArtinMatthews.SpectralABLExceptionalMassBound
public import ArtinMatthews.SpectralABLBareDiagonal


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set
noncomputable section

theorem spectralABLExceptionalCorrected_mass_le (a : ℝ) {A : ℕ} (hA : 3 ≤ A) :
    (∫ t : ℝ, ‖spectralABLExceptionalCorrected a A (t : ℂ)‖ ∂spectralKLSpectralMeasure) ≤
      spectralABLExceptionalBound A / Real.pi := by
  have hm : Measurable (fun t : ℝ => spectralABLExceptionalCorrected a A (t : ℂ)) :=
    (spectralABLExceptionalCorrected_real_contDiff a (show 1 ≤ A by omega)).continuous.measurable
  have htransfer := spectralKLCosh_integral_norm_le
    (fun t : ℝ => spectralABLExceptionalCorrected a A (t : ℂ))
    (spectralABLExceptionalWindowReal a A) hm
    (fun t _ => spectralABLExceptionalWindowReal_nonneg a A t)
    (spectralABLExceptionalWindowReal_first_moment_integrable a hA)
    (fun t _ => (spectralABLExceptionalCorrected_norm_real a A t).le)
  refine htransfer.trans ?_
  calc
    _ ≤ (2 / Real.pi ^ 2) * (spectralABLExceptionalBound A * (Real.pi / 2)) :=
      mul_le_mul_of_nonneg_left (spectralABLExceptionalWindowReal_first_moment_integral_le a hA)
        (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero] <;> ring

theorem spectralABLExceptionalBareDiagonal_norm_le (a : ℝ) {A : ℕ} (hA : 3 ≤ A) :
    ‖spectralABLBareDiagonal (spectralABLExceptionalCorrected a A)‖ ≤
      spectralABLExceptionalBound A / Real.pi := by
  exact (norm_integral_le_integral_norm _).trans (spectralABLExceptionalCorrected_mass_le a hA)

theorem spectralABLExceptionalHeatDiagonal_uniform_norm_le
    (a : ℝ) {A : ℕ} (hA : 3 ≤ A) (R : ℝ) :
    ‖spectralABLHeatDiagonal (spectralABLExceptionalCorrected a A) R‖ ≤
      spectralABLExceptionalBound A / Real.pi := by
  exact (spectralABLHeatDiagonal_norm_le _
    (spectralABLExceptionalCorrected_integrable a A hA) R).trans
      (spectralABLExceptionalCorrected_mass_le a hA)

end
end ArtinMatthews
