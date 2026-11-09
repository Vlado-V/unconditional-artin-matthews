module

public import ArtinMatthews.CubicSieveSourceModelDecay


set_option backward.privateInPublic true
@[expose] public section

/-! Finite scalar envelopes for the value and tangent marking errors. -/

noncomputable section
namespace ArtinMatthews

theorem cubicSieve_marking_value_envelope {L y q M v c : ℝ}
    (hL : 0 ≤ L) (hy : 0 < y) (hq : 0 ≤ q) (hM : 0 ≤ M) (hv : 0 < v) (hc : 0 ≤ c) :
    2 * Real.exp (8 * M) * q + (1 / v + 1 / 2) *
      (M / y + c * L / (Real.log (3 / 2 : ℝ) * y)) ≤
      (2 * Real.exp (8 * M) + (1 / v + 1 / 2) * M +
        (1 / v + 1 / 2) * c / Real.log (3 / 2 : ℝ)) * (q + (1 + L) / y) := by
  let E := q + (1 + L) / y
  have hlog : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hqE : q ≤ E := le_add_of_nonneg_right (div_nonneg (by linarith) hy.le)
  have h1E : 1 / y ≤ E := by
    exact (div_le_div_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + L) hy.le).trans
      (le_add_of_nonneg_left hq)
  have hLE : L / y ≤ E := by
    exact (div_le_div_of_nonneg_right (by linarith : L ≤ 1 + L) hy.le).trans
      (le_add_of_nonneg_left hq)
  have h₁ := mul_le_mul_of_nonneg_left hqE (by positivity : 0 ≤ 2 * Real.exp (8 * M))
  have h₂ := mul_le_mul_of_nonneg_left h1E (by positivity : 0 ≤ (1 / v + 1 / 2) * M)
  have h₃ := mul_le_mul_of_nonneg_left hLE
    (by positivity : 0 ≤ (1 / v + 1 / 2) * c / Real.log (3 / 2 : ℝ))
  dsimp only [E] at h₁ h₂ h₃
  convert add_le_add (add_le_add h₁ h₂) h₃ using 1 <;> ring

theorem cubicSieve_marking_tangent_envelope {L y q M v Z K : ℝ}
    (hy : 0 < y) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hM : 0 ≤ M) (hv : 0 < v) (hK : 0 ≤ K) (hZ : 0 ≤ Real.log Z)
    (hZL : Real.log Z ≤ 2 * L) :
    2 * (4 * Real.log Z / y) * (K + 1) * Real.exp (8 * M) * q +
      (1 / v + 1 / 2) * (2 * Real.log Z * M / y) ≤
      (16 * (K + 1) * Real.exp (8 * M) + 4 * (1 / v + 1 / 2) * M) *
        (q + (1 + L) / y) := by
  have hlogq : Real.log Z * q ≤ 2 * L :=
    (mul_le_of_le_one_right hZ hq1).trans hZL
  have h₁ := mul_le_mul_of_nonneg_left hlogq
    (by positivity : 0 ≤ 8 * (K + 1) * Real.exp (8 * M) / y)
  have h₂ := mul_le_mul_of_nonneg_left hZL
    (by positivity : 0 ≤ 2 * (1 / v + 1 / 2) * M / y)
  have hLE : L / y ≤ q + (1 + L) / y :=
    (div_le_div_of_nonneg_right (by linarith : L ≤ 1 + L) hy.le).trans (le_add_of_nonneg_left hq)
  have h₃ := mul_le_mul_of_nonneg_left hLE
    (by positivity : 0 ≤ 16 * (K + 1) * Real.exp (8 * M) + 4 * (1 / v + 1 / 2) * M)
  calc
    _ ≤ (16 * (K + 1) * Real.exp (8 * M) + 4 * (1 / v + 1 / 2) * M) * (L / y) := by
      convert add_le_add h₁ h₂ using 1 <;> ring
    _ ≤ _ := h₃

end ArtinMatthews
