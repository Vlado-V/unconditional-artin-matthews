module

public import ArtinMatthews.SpectralABLCorrectedInverse
public import ArtinMatthews.SpectralABLLiteralInverse
public import ArtinMatthews.SpectralKLWindowDerivatives
public import ArtinMatthews.SpectralKLWindowLinearity
public import ArtinMatthews.SpectralKLBoundedMultiplierIntegral


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem spectralABLRegularInverse_contDiffOn (T ε : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContDiffOn ℝ ∞ (spectralABLRegularInverse T ε g) (Ioi (0 : ℝ)) := by
  let Δ := T ^ (1 - ε)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT _
  have hb := spectralABLRegularWindow_norm_le hT hΔ
  have hC : 0 ≤ spectralABLRegularBound T Δ := (norm_nonneg _).trans (hb 0)
  exact spectralKLWindowSynthesis_contDiffOn (spectralABLRegularWindow T Δ) g
    (spectralABLRegularWindow_real_continuous T Δ) hg hc hp _ hC
    (fun t => (hb t).trans (le_mul_of_one_le_right hC (by nlinarith [sq_nonneg t])))

theorem spectralABLExceptionalInverse_contDiffOn (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContDiffOn ℝ ∞ (spectralABLExceptionalInverse a A g) (Ioi (0 : ℝ)) := by
  have hb := spectralABLExceptionalWindow_norm_le a hA
  have hC : 0 ≤ spectralABLExceptionalBound A := (norm_nonneg _).trans (hb 0)
  exact spectralKLWindowSynthesis_contDiffOn (spectralABLExceptionalWindow a A) g
    (spectralABLExceptionalWindow_real_continuous a hA) hg hc hp _ hC
    (fun t => (hb t).trans (le_mul_of_one_le_right hC (by nlinarith [sq_nonneg t])))

theorem spectralABLRegularCorrectedProfile_contDiffOn (T ε : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContDiffOn ℝ ∞ (spectralABLRegularCorrectedProfile T ε g) (Ioi (0 : ℝ)) := by
  let Δ := T ^ (1 - ε)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT _
  obtain ⟨H, hH, hb⟩ := spectralABLRegularCorrected_strip_bound T Δ hT hΔ
  have hbound (t : ℝ) : ‖spectralABLRegularCorrected T Δ (t : ℂ)‖ ≤ H * (1 + t ^ 2) := by
    have hr := hb t 0 (by norm_num)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hr
    exact hr.trans (le_mul_of_one_le_right hH (by nlinarith [sq_nonneg t]))
  exact spectralKLWindowSynthesis_contDiffOn (spectralABLRegularCorrected T Δ) g
    (spectralABLRegularCorrected_real_contDiff T Δ).continuous hg hc hp H hH hbound

theorem spectralABLExceptionalCorrectedProfile_contDiffOn (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ContDiffOn ℝ ∞ (spectralABLExceptionalCorrectedProfile a A g) (Ioi (0 : ℝ)) := by
  obtain ⟨H, hH, hb⟩ := spectralABLExceptionalCorrected_strip_bound a hA
  have hbound (t : ℝ) : ‖spectralABLExceptionalCorrected a A (t : ℂ)‖ ≤ H * (1 + t ^ 2) := by
    have hr := hb t 0 (by norm_num)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hr
    exact hr.trans (le_mul_of_one_le_right hH (by nlinarith [sq_nonneg t]))
  exact spectralKLWindowSynthesis_contDiffOn (spectralABLExceptionalCorrected a A) g
    (spectralABLExceptionalCorrected_real_contDiff a hA).continuous hg hc hp H hH hbound


theorem spectralABLRegularInverse_rapid_decay (T ε : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖spectralABLRegularInverse T ε g x‖ ≤ C / x ^ k := by
  let Δ := T ^ (1 - ε)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT _
  have hb := spectralABLRegularWindow_norm_le hT hΔ
  have hC : 0 ≤ spectralABLRegularBound T Δ := (norm_nonneg _).trans (hb 0)
  exact spectralKLWindowSynthesis_large_bound (spectralABLRegularWindow T Δ) g hg hc hp _ hC
    (fun t => (hb t).trans (le_mul_of_one_le_right hC (by nlinarith [sq_nonneg t]))) k hk

theorem spectralABLExceptionalInverse_rapid_decay (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖spectralABLExceptionalInverse a A g x‖ ≤ C / x ^ k := by
  have hb := spectralABLExceptionalWindow_norm_le a hA
  have hC : 0 ≤ spectralABLExceptionalBound A := (norm_nonneg _).trans (hb 0)
  exact spectralKLWindowSynthesis_large_bound (spectralABLExceptionalWindow a A) g hg hc hp _ hC
    (fun t => (hb t).trans (le_mul_of_one_le_right hC (by nlinarith [sq_nonneg t]))) k hk

theorem spectralABLRegularCorrectedProfile_rapid_decay (T ε : ℝ) (hT : 0 < T)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖spectralABLRegularCorrectedProfile T ε g x‖ ≤ C / x ^ k := by
  let Δ := T ^ (1 - ε)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hT _
  obtain ⟨H, hH, hb⟩ := spectralABLRegularCorrected_strip_bound T Δ hT hΔ
  have hbound (t : ℝ) : ‖spectralABLRegularCorrected T Δ (t : ℂ)‖ ≤ H * (1 + t ^ 2) := by
    have hr := hb t 0 (by norm_num)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hr
    exact hr.trans (le_mul_of_one_le_right hH (by nlinarith [sq_nonneg t]))
  exact spectralKLWindowSynthesis_large_bound (spectralABLRegularCorrected T Δ) g hg hc hp H hH hbound k hk

theorem spectralABLExceptionalCorrectedProfile_rapid_decay (a : ℝ) (A : ℕ) (hA : 1 ≤ A)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖spectralABLExceptionalCorrectedProfile a A g x‖ ≤ C / x ^ k := by
  obtain ⟨H, hH, hb⟩ := spectralABLExceptionalCorrected_strip_bound a hA
  have hbound (t : ℝ) : ‖spectralABLExceptionalCorrected a A (t : ℂ)‖ ≤ H * (1 + t ^ 2) := by
    have hr := hb t 0 (by norm_num)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at hr
    exact hr.trans (le_mul_of_one_le_right hH (by nlinarith [sq_nonneg t]))
  exact spectralKLWindowSynthesis_large_bound (spectralABLExceptionalCorrected a A) g hg hc hp H hH hbound k hk

end
end ArtinMatthews
