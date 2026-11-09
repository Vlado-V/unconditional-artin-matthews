module

public import ArtinMatthews.SpectralKLInverseIEnvelope


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem spectralKLWindowData_rapid (h : ℂ → ℂ) (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ioi (0 : ℝ))
    (H : ℝ) (hH : 0 ≤ H) (hh : ∀ t : ℝ, ‖h (t : ℂ)‖ ≤ H * (1 + t ^ 2)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) *
      ‖spectralKLWindowData h g t‖ ≤ C := by
  obtain ⟨K, hK, hk⟩ := spectralKLCompactOrderTransform_strip_rapid g hg hc hp (N + 1)
  refine ⟨H * K, mul_nonneg hH hK, ?_⟩
  intro t
  have hκ := hk 0 t (by norm_num)
  simp only [Complex.ofReal_zero, neg_zero, zero_add] at hκ
  rw [spectralKLWindowData, norm_mul]
  calc
    _ ≤ (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) *
        ((H * (1 + t ^ 2)) * ‖spectralKLCompactOrderTransform g ((t : ℂ) * Complex.I)‖) := by
      gcongr
      exact hh t
    _ = H * ((1 + t ^ 2) ^ (N + 1) * Real.exp (Real.pi * |t| / 2) *
        ‖spectralKLCompactOrderTransform g ((t : ℂ) * Complex.I)‖) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hκ hH

end
end ArtinMatthews
