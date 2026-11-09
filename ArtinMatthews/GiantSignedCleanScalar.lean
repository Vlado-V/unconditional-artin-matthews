module

public import ArtinMatthews.GiantSignedTiltError


set_option backward.privateInPublic true
@[expose] public section

/-! The exact density prefactor and the additive norm errors give the
source factor two once the actual errors are sufficiently small. -/
namespace ArtinMatthews
noncomputable section

theorem giantSignedCleanScalar_two
    (δ U E : ℝ) (dim : ℕ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hsmall : (dim : ℝ) * δ ≤ 1 / 2)
    (hU : 0 ≤ U) (hE : 0 ≤ E) (herr : E ≤ U / 4) :
    ((1 - δ)⁻¹) ^ dim * (U + E) ^ 2 ≤ (2 * U) ^ 2 := by
  have hR : ((1 - δ)⁻¹) ^ dim ≤ 2 := by
    have h := giantSignedTilt_inverse_pow_error δ hδ hδ1 dim hsmall
    linarith
  have hs : U + E ≤ (5 / 4 : ℝ) * U := by linarith
  have hsq := pow_le_pow_left₀ (add_nonneg hU hE) hs 2
  calc
    _ ≤ 2 * (U + E) ^ 2 := mul_le_mul_of_nonneg_right hR (sq_nonneg _)
    _ ≤ 2 * ((5 / 4 : ℝ) * U) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ ≤ _ := by nlinarith [sq_nonneg U]

end
end ArtinMatthews
