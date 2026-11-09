module

public import ArtinMatthews.ShiftedABLRhoFullSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Integrating a polynomial bound for the true common-test packet
uses its fixed Schwartz density, with unrestricted Mellin heights. -/

noncomputable section
open Set MeasureTheory OAI
namespace ArtinMatthews

theorem shiftedABLMellinSignedSum_norm_le_of_full_separated
    (χ : SevenEighths.HeckeFamily.Character) (D m3 m4 F r L : ℕ)
    (hne : m3 ≠ m4) (hF : 0 < F) (hr : 0 < r) (hL : 0 < L) (hcop : r.Coprime F)
    (d : ℕ × ℕ) (i : ℕ × Bool) (z : ℝ × ℝ) (J : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hBound : ∀ t : ℝ, ‖shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t‖ ≤
      B*(1+‖t+shiftedABLRhoHeight z‖)^J) :
    ‖shiftedABLMellinSignedSum χ D m3 m4 F r L d i z‖ ≤
      (2 : ℝ)^J*shiftedABLRhoFourierMoment J*B*(1+‖z.1‖+‖z.2‖)^J := by
  obtain ⟨hI,hEq⟩ := shiftedABLMellinSignedSum_full_rho_separation χ D m3 m4 F r L
    hne hF hr hL hcop d i z
  obtain ⟨hM,hMB⟩ := shiftedABLRhoFourier_shiftedMoment_le z J
  let P (t : ℝ) := (1+‖t+shiftedABLRhoHeight z‖)^J*‖shiftedABLRhoFourierDensity t‖
  have hDom (t : ℝ) : ‖shiftedABLRhoFourierDensity t*
      shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t‖ ≤ B*P t := by
    rw [norm_mul]
    calc
      _ ≤ ‖shiftedABLRhoFourierDensity t‖*(B*(1+‖t+shiftedABLRhoHeight z‖)^J) :=
        mul_le_mul_of_nonneg_left (hBound t) (norm_nonneg _)
      _ = _ := by dsimp only [P]; ring
  rw [hEq]
  have hMoment : 0 ≤ shiftedABLRhoFourierMoment J := integral_nonneg (fun _ => by positivity)
  have hZ : 1+2*(‖z.1‖+‖z.2‖) ≤ 2*(1+‖z.1‖+‖z.2‖) := by linarith
  calc
    _ ≤ ∫ t : ℝ, ‖shiftedABLRhoFourierDensity t*
        shiftedABLFullSeparatedSignedSum χ D m3 m4 F r L d i z t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, B*P t := integral_mono hI.norm (hM.const_mul B) hDom
    _ = B*(∫ t : ℝ, P t) := integral_const_mul _ _
    _ ≤ B*((1+2*(‖z.1‖+‖z.2‖))^J*shiftedABLRhoFourierMoment J) :=
      mul_le_mul_of_nonneg_left hMB hB
    _ ≤ B*((2*(1+‖z.1‖+‖z.2‖))^J*shiftedABLRhoFourierMoment J) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hZ J) hMoment) hB
    _ = _ := by rw [mul_pow]; ring

end ArtinMatthews
