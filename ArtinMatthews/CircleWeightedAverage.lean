module

public import ArtinMatthews.CircleDetector


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite interchange puts the circle approximation in the form used
by the individual-modulus double Voronoi identities. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem circleDetector_sum_eq_average {ι : Type*} (S : Finset ι)
    (A : ι → ℂ) (frequency : ι → ℤ) (Q : Finset ℕ) (ω : ℕ → ℝ) :
    (∑ k∈S, A k*circleDetector Q ω (frequency k)) =
      (∑ q∈Q, (ω q : ℂ)*(∑ k∈S, A k*primitiveCircleSum q (frequency k))) /
        (circleNormalizer Q ω : ℂ) := by
  simp only [circleDetector,← mul_div_assoc,Finset.mul_sum,← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro k _
  ring

end ArtinMatthews
