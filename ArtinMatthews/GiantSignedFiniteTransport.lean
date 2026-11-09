module

public import ArtinMatthews.IdealProductAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted finite transport with its exact input and output masses. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedFiniteTransport_energy
    {X Y : Type*} [Fintype X] [Fintype Y]
    (sourceMass : X → ℝ) (targetMass : Y → ℝ) (q : X → Y → ℝ)
    (hsource : ∀ x, 0 ≤ sourceMass x) (hq : ∀ x y, 0 ≤ q x y)
    (hrow : ∀ x, ∑ y, q x y = 1)
    (hpush : ∀ y, ∑ x, sourceMass x * q x y = targetMass y)
    (K : X → Y → ℂ) (C : ℝ) (hK : ∀ x y, ‖K x y‖ ≤ C) (f : Y → ℂ) :
    (∑ x, sourceMass x * ‖∑ y, (q x y : ℂ) * K x y * f y‖ ^ 2) ≤
      C ^ 2 * ∑ y, targetMass y * ‖f y‖ ^ 2 := by
  classical
  have hp (x : X) : ‖∑ y, (q x y : ℂ) * K x y * f y‖ ^ 2 ≤
      ∑ y, q x y * (C ^ 2 * ‖f y‖ ^ 2) := by
    have hj := idealWeightedJensen (q x) (hq x) (hrow x) (fun y => K x y * f y)
    simp only [← mul_assoc] at hj
    apply hj.trans
    apply Finset.sum_le_sum
    intro y _
    apply mul_le_mul_of_nonneg_left _ (hq x y)
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hK x y))).mpr (hK x y))
      (sq_nonneg ‖f y‖)
  calc
    _ ≤ ∑ x, sourceMass x * ∑ y, q x y * (C ^ 2 * ‖f y‖ ^ 2) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hp x) (hsource x)
    _ = ∑ y, targetMass y * (C ^ 2 * ‖f y‖ ^ 2) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      simp only [← mul_assoc, ← Finset.sum_mul, hpush]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

end
end ArtinMatthews
