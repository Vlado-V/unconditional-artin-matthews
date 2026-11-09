module

public import ArtinMatthews.ShiftedABLMellinProfileDerivatives


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial losses in the two Mellin heights are integrated against
the actual Schwartz kernels. -/

noncomputable section
open MeasureTheory Set
namespace ArtinMatthews

theorem shiftedABLMellin_integral_bound (F : ℝ × ℝ → ℂ)
    (b1 b2 : SchwartzMap ℝ ℂ) (J : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ z, ‖F z‖ ≤ B*(1+|z.1|+|z.2|)^J) :
    ‖∫ z : ℝ × ℝ, F z*(b1 z.1*b2 z.2)‖ ≤
      B*(∫ t : ℝ, (1+‖t‖)^J*‖b1 t‖)*(∫ t : ℝ, (1+‖t‖)^J*‖b2 t‖) := by
  let w (z : ℝ × ℝ) := (1+|z.1|+|z.2|)^J*(‖b1 z.1‖*‖b2 z.2‖)
  obtain ⟨hw,hbound⟩ := shiftedABLMellin_product_moment_bound b1 b2 J
  have hpoint (z : ℝ × ℝ) : ‖F z*(b1 z.1*b2 z.2)‖ ≤ B*w z := by
    rw [norm_mul,norm_mul]
    exact (mul_le_mul_of_nonneg_right (hF z) (by positivity)).trans_eq (by dsimp [w]; ring)
  calc
    _ ≤ ∫ z : ℝ × ℝ, B*w z :=
      norm_integral_le_of_norm_le (hw.const_mul B) (ae_of_all _ hpoint)
    _ = B*(∫ z : ℝ × ℝ, w z) := integral_const_mul B w
    _ ≤ B*((∫ t : ℝ, (1+‖t‖)^J*‖b1 t‖)*(∫ t : ℝ, (1+‖t‖)^J*‖b2 t‖)) :=
      mul_le_mul_of_nonneg_left hbound hB
    _ = _ := by ring

end ArtinMatthews
