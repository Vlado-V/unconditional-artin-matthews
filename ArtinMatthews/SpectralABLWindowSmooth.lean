module

public import ArtinMatthews.SpectralABLCorrectedWindows
public import Mathlib.Analysis.Complex.CauchyIntegral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

theorem spectral_real_contDiff_of_order_strip (h : ℂ → ℂ) (ε : ℝ) (hε : 0 < ε)
    (hh : ∀ z : ℂ, |z.im| < ε → DifferentiableAt ℂ h z) :
    ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ)) := by
  let S : Set ℂ := {z | |z.im| < ε}
  have ho : IsOpen S := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hd : DifferentiableOn ℂ h S := fun z hz => (hh z hz).differentiableWithinAt
  have hc : ContDiffOn ℂ ∞ h S := hd.contDiffOn ho
  rw [contDiff_iff_contDiffAt]
  intro t
  have ht : (t : ℂ) ∈ S := by simpa only [S, mem_ofPred_eq, Complex.ofReal_im, abs_zero] using hε
  exact ((hc.contDiffAt (ho.mem_nhds ht)).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt

theorem spectralABLRegularWindow_real_contDiff (T Δ : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralABLRegularWindow T Δ (t : ℂ)) :=
  (spectralABLRegularWindow_differentiable T Δ).contDiff.restrict_scalars ℝ |>.comp Complex.ofRealCLM.contDiff

theorem spectralABLExceptionalWindow_real_contDiff (a : ℝ) {A : ℕ} (hA : 1 ≤ A) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralABLExceptionalWindow a A (t : ℂ)) := by
  apply spectral_real_contDiff_of_order_strip _ (2 * A) (by exact_mod_cast (by omega : 0 < 2 * A))
  exact spectralABLExceptionalWindow_differentiableAt a A

theorem spectralABLRegularCorrected_real_contDiff (T Δ : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralABLRegularCorrected T Δ (t : ℂ)) :=
  spectral_real_contDiff_of_order_strip _ (3 / 2) (by norm_num)
    (spectralABLRegularCorrected_differentiableAt T Δ)

theorem spectralABLExceptionalCorrected_real_contDiff (a : ℝ) {A : ℕ} (hA : 1 ≤ A) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralABLExceptionalCorrected a A (t : ℂ)) :=
  spectral_real_contDiff_of_order_strip _ (3 / 2) (by norm_num)
    (spectralABLExceptionalCorrected_differentiableAt a hA)

end
end ArtinMatthews
