module

public import ArtinMatthews.SpectralCompactLaplace


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Complex
open scoped ContDiff
noncomputable section

theorem spectralCompactLaplace_iterated_properties (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ici (0 : ℝ)) (N : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv N g) ∧ HasCompactSupport (iteratedDeriv N g) ∧
      tsupport (iteratedDeriv N g) ⊆ Ici (0 : ℝ) := by
  induction N with
  | zero => simpa only [iteratedDeriv_zero] using ⟨hg,hc,hp⟩
  | succ N ih =>
    rw [iteratedDeriv_succ]
    exact ⟨(contDiff_infty_iff_deriv.mp ih.1).2,ih.2.1.deriv,tsupport_deriv_subset.trans ih.2.2⟩

/-- The scaled decay bound follows from literal compact integration by parts. -/
theorem spectralCompactLaplace_scaled_norm_le (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hp : tsupport g ⊆ Ici (0 : ℝ))
    (N : ℕ) {b : ℝ} (hb : 0 ≤ b) {z : ℂ} (hz : 0 ≤ z.re) :
    (1+b*‖z‖)^N*‖spectralCompactLaplace g z‖ ≤
      2^N*((∫ x : ℝ, ‖g x‖)+b^N*(∫ x : ℝ, ‖iteratedDeriv N g x‖)) := by
  let M := ∫ x : ℝ, ‖g x‖
  let D := ∫ x : ℝ, ‖iteratedDeriv N g x‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => norm_nonneg _)
  have hD : 0 ≤ D := integral_nonneg (fun _ => norm_nonneg _)
  have h₀ : ‖spectralCompactLaplace g z‖ ≤ M :=
    spectralCompactLaplace_norm_le g hg.continuous hc hp hz
  obtain ⟨hN,hcN,hpN⟩ := spectralCompactLaplace_iterated_properties g hg hc hp N
  have hN' : ‖z‖^N*‖spectralCompactLaplace g z‖ ≤ D := by
    rw [← norm_pow,← norm_mul,← spectralCompactLaplace_iteratedDeriv g hg hc N z]
    exact spectralCompactLaplace_norm_le _ hN.continuous hcN hpN hz
  change (1+b*‖z‖)^N*‖spectralCompactLaplace g z‖ ≤ 2^N*(M+b^N*D)
  by_cases hs : b*‖z‖ ≤ 1
  · have hp' : (1+b*‖z‖)^N ≤ (2 : ℝ)^N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    exact (mul_le_mul hp' h₀ (norm_nonneg _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
  · have hp' : (1+b*‖z‖)^N ≤ (2*(b*‖z‖))^N :=
      pow_le_pow_left₀ (by positivity) (by linarith [lt_of_not_ge hs]) N
    calc
      _ ≤ (2*(b*‖z‖))^N*‖spectralCompactLaplace g z‖ :=
        mul_le_mul_of_nonneg_right hp' (norm_nonneg _)
      _ = 2^N*b^N*(‖z‖^N*‖spectralCompactLaplace g z‖) := by rw [mul_pow,mul_pow]; ring
      _ ≤ 2^N*b^N*D := mul_le_mul_of_nonneg_left hN' (by positivity)
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hM) (by positivity)

end
end ArtinMatthews
