module

public import ArtinMatthews.MarkedEstimateDeweighting


set_option backward.privateInPublic true
@[expose] public section

/-! Moving the positive model mean outside a finite marked correlation. -/

namespace ArtinMatthews

open scoped BigOperators

theorem marked_normalized_sum_eq {U : Type*} (S : Finset U)
    (a : U → ℂ) (w : U → ℝ) (m : ℝ) :
    (∑ u ∈ S, a u * ((w u / m : ℝ) : ℂ)) =
      (∑ u ∈ S, a u * (w u : ℂ)) / (m : ℂ) := by
  simp_rw [Complex.ofReal_div, ← mul_div_assoc]
  rw [Finset.sum_div]

theorem marked_normalized_sum_norm {U : Type*} (S : Finset U)
    (a : U → ℂ) (w : U → ℝ) {m : ℝ} (hm : 0 ≤ m) :
    ‖∑ u ∈ S, a u * ((w u / m : ℝ) : ℂ)‖ =
      ‖∑ u ∈ S, a u * (w u : ℂ)‖ / m := by
  rw [marked_normalized_sum_eq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm]

theorem marked_normalized_sum_scale {U : Type*} (S : Finset U)
    (a : U → ℂ) (w : U → ℝ) {m : ℝ} (hm : 0 ≤ m) (x : ℝ) :
    Real.log x / x * ‖∑ u ∈ S, a u * ((w u / m : ℝ) : ℂ)‖ =
      Real.log x / (x * m) * ‖∑ u ∈ S, a u * (w u : ℂ)‖ := by
  rw [marked_normalized_sum_norm S a w hm]
  ring

end ArtinMatthews
