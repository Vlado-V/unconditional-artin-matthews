module

public import ArtinMatthews.ShiftedVoronoiBesselInversion
public import ArtinMatthews.ShiftedVoronoiBesselDecay


set_option backward.privateInPublic true
@[expose] public section

/-!
# Weight-one Bessel inversion for general compact smooth tests

The hypotheses below express `H ∈ C∞c((0,∞))` directly: smoothness on the
real line and support in a compact interval whose left endpoint is positive.
The Schwartz structure used by Fourier theory is constructed from these
hypotheses, and all integral-convergence obligations are discharged.
-/

noncomputable section
open MeasureTheory Set Complex
open scoped ContDiff

namespace ArtinMatthews

theorem weightOneBesselTransform_gamma_inversion_of_smooth_compact
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) (σ y : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hy : 0 < y) :
    weightOneBesselTransform H y = ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      mellinInv σ (fun s ↦ (Complex.Gamma s / Complex.Gamma (1 - s)) *
        mellin H (1 - s)) (4 * Real.pi ^ 2 * y) := by
  have hK : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hHs
  exact weightOneBesselTransform_gamma_inversion
    (hK.toSchwartzMap hH) a b ha hHs σ y hσ hσ1 hy

theorem weightOneBesselTransform_rapid_decay_of_smooth_compact
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y →
      (1 + y) ^ A * ‖weightOneBesselTransform H y‖ ≤ C := by
  have hK : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hHs
  apply weightOneBesselTransform_rapid_decay (hK.toSchwartzMap hH)
    (max b 0) (le_max_right _ _)
  intro x hx
  have hh := hHs hx
  exact ⟨ha.le.trans hh.1, hh.2.trans (le_max_left _ _)⟩

end ArtinMatthews
