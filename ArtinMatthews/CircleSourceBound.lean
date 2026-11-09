module

public import ArtinMatthews.CircleShiftedFrequency


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial source-mass envelope for the finite circle approximation. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem circleShifted_bounded_approximation (m3 m4 K1 K2 : ℕ)
    (a : ℕ×ℕ → ℂ) (A : ℝ)
    (ha : ∀ k∈(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2), ‖a k‖≤A)
    (Q : Finset ℕ) (ω : ℕ → ℝ)
    (hω : ∀ q∈Q, 0≤ω q) (hΛ : 0<circleNormalizer Q ω) :
    ‖(∑ k∈(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2),
        a k*circleDetector Q ω (circleShiftedFrequency m3 m4 k)) -
      (∑ k∈((Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2)).filter
        (fun k => circleShiftedFrequency m3 m4 k=0), a k)‖ ≤
      (K1 : ℝ)*(K2 : ℝ)*A *
        (circleWeightMass Q ω*((m4*K1+m3*K2 : ℕ) : ℝ)^2/circleNormalizer Q ω) := by
  apply (circleShifted_finite_approximation m3 m4 K1 K2 a Q ω hω hΛ).trans
  apply mul_le_mul_of_nonneg_right
  · calc
      _ ≤ ∑ _k∈(Finset.Icc 1 K1) ×ˢ (Finset.Icc 1 K2), A := Finset.sum_le_sum ha
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_product,
        Nat.card_Icc,Nat.add_one_sub_one,Nat.cast_mul]
  · exact div_nonneg (mul_nonneg (circleWeightMass_nonneg Q ω hω) (sq_nonneg _)) hΛ.le

end ArtinMatthews
