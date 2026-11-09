module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Order


set_option backward.privateInPublic true
@[expose] public section

/-! A finite ordered retrieval count is controlled by the remaining-hit
damping, uniformly in the old memory degree. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedPromotionDamping_bound (a z : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (z.descFactorial a : ℝ) * ρ ^ (z - a) ≤
      (a.factorial : ℝ) / (1 - ρ) ^ (a + 1) := by
  by_cases ha : a ≤ z
  · have hr : ‖ρ‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hρ]
    have hs := hasSum_choose_mul_geometric_of_norm_lt_one a hr
    have ht : ((z - a + a).choose a : ℝ) * ρ ^ (z - a) ≤
        1 / (1 - ρ) ^ (a + 1) := by
      simpa only [Finset.sum_singleton] using
        sum_le_hasSum ({z - a} : Finset ℕ)
          (fun n _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ _)) hs
    rw [Nat.sub_add_cancel ha] at ht
    calc
      (z.descFactorial a : ℝ) * ρ ^ (z - a) =
          (a.factorial : ℝ) * ((z.choose a : ℝ) * ρ ^ (z - a)) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc]
      _ ≤ (a.factorial : ℝ) * (1 / (1 - ρ) ^ (a + 1)) :=
        mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
      _ = _ := by rw [mul_one_div]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge ha), Nat.cast_zero, zero_mul]
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_pos.mpr hρ1).le _)

theorem giantSignedPromotionFactor_mono (a t : ℕ) (ha : a ≤ t) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (a.factorial : ℝ) / (1 - ρ) ^ (a + 1) ≤
      (t.factorial : ℝ) / (1 - ρ) ^ (t + 1) := by
  have hd : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hi : 1 ≤ (1 - ρ)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hd).mpr
    linarith
  simp only [div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul
    (Nat.cast_le.mpr (Nat.factorial_le ha))
    (pow_le_pow_right₀ hi (Nat.add_le_add_right ha 1))
    (pow_nonneg (inv_nonneg.mpr hd.le) _)
    (Nat.cast_nonneg _)

theorem giantSignedPromotionDamping_uniform (a z t : ℕ) (ha : a ≤ t) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (z.descFactorial a : ℝ) * ρ ^ (z - a) ≤
      (t.factorial : ℝ) / (1 - ρ) ^ (t + 1) :=
  (giantSignedPromotionDamping_bound a z hρ hρ1).trans
    (giantSignedPromotionFactor_mono a t ha hρ hρ1)

end
end ArtinMatthews
