module

public import ArtinMatthews.PrimeExtractionSquareful


set_option backward.privateInPublic true
@[expose] public section

/-! All-logarithmic negligibility of the actual rough squareful set. -/

namespace ArtinMatthews

open Filter
open scoped Asymptotics Topology

noncomputable def roughNonsquarefreeCount (T γ x : ℝ) : ℝ :=
  ((roughNonsquarefreeUpTo ⌊T * x⌋₊ (x ^ γ)).card : ℝ)

theorem roughNonsquarefreeCount_eventual_bound {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, roughNonsquarefreeCount T γ x ≤ 4 * T * x / x ^ γ := by
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    (tendsto_rpow_atTop hγ).eventually (eventually_ge_atTop (4 : ℝ))] with x hx hz
  calc
    _ ≤ 4 * (⌊T * x⌋₊ : ℝ) / x ^ γ := roughNonsquarefreeUpTo_card_le _ hz
    _ ≤ 4 * (T * x) / x ^ γ := by
      gcongr
      exact Nat.floor_le (mul_nonneg hT hx)
    _ = _ := by ring

theorem roughNonsquarefreeCount_all_log_tendsto {T γ : ℝ}
    (hT : 0 ≤ T) (hγ : 0 < γ) (A : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ A / x * roughNonsquarefreeCount T γ x)
      atTop (𝓝 0) := by
  have hlim := (isLittleO_log_rpow_rpow_atTop A hγ).tendsto_div_nhds_zero.const_mul (4 * T)
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg (Real.log_pos hx).le _) (by linarith))
      (Nat.cast_nonneg _)
  · filter_upwards [roughNonsquarefreeCount_eventual_bound hT hγ,
      eventually_gt_atTop (1 : ℝ)] with x hcount hx
    have hx0 : 0 < x := by linarith
    calc
      _ ≤ (Real.log x) ^ A / x * (4 * T * x / x ^ γ) :=
        mul_le_mul_of_nonneg_left hcount
          (div_nonneg (Real.rpow_nonneg (Real.log_pos hx).le _) hx0.le)
      _ = _ := by field_simp

/-- The exceptional set in the first paragraph of Proposition 8.1 has
o(x/log^A x) elements for every fixed A and every positive roughness exponent. -/
theorem roughNonsquarefreeCount_isLittleO {T γ : ℝ}
    (hT : 0 ≤ T) (hγ : 0 < γ) (A : ℝ) :
    roughNonsquarefreeCount T γ =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun h => (mul_pos (by linarith : 0 < x)
      (Real.rpow_pos_of_pos (Real.log_pos hx) (-A))).ne' h |>.elim
  · apply (roughNonsquarefreeCount_all_log_tendsto hT hγ A).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_neg (Real.log_pos hx).le]
    field_simp

end ArtinMatthews
