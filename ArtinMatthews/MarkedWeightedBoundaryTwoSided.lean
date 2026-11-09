module

public import ArtinMatthews.MarkedWeightedOperatorWord


set_option backward.privateInPublic true
@[expose] public section

/-! Cauchy for two independently bounded endpoint vectors. A bounded
initial birth phase changes only the left vector; the right vector keeps
its original literal empty-memory boundary. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedWeightedBoundary_two_sided_norm_le {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ s, 0 ≤ μ s) (b₀ b₁ f : Ω → ℂ)
    {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb₀ : (∑ s, μ s*‖b₀ s‖^2) ≤ D) (hb₁ : (∑ s, μ s*‖b₁ s‖^2) ≤ D)
    (hf : (∑ s, μ s*‖f s‖^2) ≤ C^2*∑ s, μ s*‖b₁ s‖^2) :
    ‖∑ s, (μ s:ℂ)*star (b₀ s)*f s‖ ≤ D*C := by
  have hE₀ : 0 ≤ ∑ s, μ s*‖b₀ s‖^2 := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  have hE₁ : 0 ≤ ∑ s, μ s*‖b₁ s‖^2 := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD hC)).mp
  calc
    _ ≤ (∑ s, μ s*‖b₀ s‖^2)*(∑ s, μ s*‖f s‖^2) := markedWeightedBoundary_cauchy μ hμ b₀ f
    _ ≤ (∑ s, μ s*‖b₀ s‖^2)*(C^2*∑ s, μ s*‖b₁ s‖^2) := mul_le_mul_of_nonneg_left hf hE₀
    _ ≤ D*(C^2*D) := mul_le_mul hb₀ (mul_le_mul_of_nonneg_left hb₁ (sq_nonneg _))
      (mul_nonneg (sq_nonneg C) hE₁) hD
    _ = _ := by ring

theorem markedWeightedEnergy_bounded_multiplier {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ s, 0 ≤ μ s) (β f : Ω → ℂ) (hβ : ∀ s, ‖β s‖ ≤ 1) :
    (∑ s, μ s*‖β s*f s‖^2) ≤ ∑ s, μ s*‖f s‖^2 := by
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (hμ s)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hβ s) (norm_nonneg _)).trans_eq (one_mul _)

end ArtinMatthews
