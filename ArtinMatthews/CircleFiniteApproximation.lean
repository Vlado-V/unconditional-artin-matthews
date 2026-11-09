module

public import ArtinMatthews.CircleDetector


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite-sum comparison between an integer equation and the weighted
circle detector. Its error uses the actual coefficient l1 mass.
-/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem circleDetector_finite_approximation {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (frequency : ι → ℤ) (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) (hΛ : 0<circleNormalizer Q ω)
    (R : ℕ) (hR : ∀ i∈S, (frequency i).natAbs≤R) :
    ‖(∑ i∈S, a i*circleDetector Q ω (frequency i)) -
      (∑ i∈S with frequency i=0, a i)‖ ≤
    (∑ i∈S, ‖a i‖) * (circleWeightMass Q ω*(R : ℝ)^2/circleNormalizer Q ω) := by
  classical
  have heq : (∑ i∈S, a i*circleDetector Q ω (frequency i)) -
      (∑ i∈S with frequency i=0, a i) =
      ∑ i∈S, a i*(circleDetector Q ω (frequency i) -
        (if frequency i=0 then 1 else 0)) := by
    rw [Finset.sum_filter,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    split_ifs <;> ring
  rw [heq]
  calc
    _ ≤ ∑ i∈S, ‖a i*(circleDetector Q ω (frequency i) -
        (if frequency i=0 then 1 else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ i∈S, ‖a i‖*(circleWeightMass Q ω*(R : ℝ)^2/circleNormalizer Q ω) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (circleDetector_error_le Q ω hω hΛ R
        (frequency i) (hR i hi)) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

end ArtinMatthews
