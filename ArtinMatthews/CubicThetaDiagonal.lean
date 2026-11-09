module

public import ArtinMatthews.QuadraticIdealNormCountGlobal
public import ArtinMatthews.ShiftedDiagonalBound


set_option backward.privateInPublic true
@[expose] public section

/-! The actual theta-coefficient diagonal estimate in the shifted bilinear
argument. The constant is uniform in the finite-conductor ideal character.
-/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem idealTheta_diagonal_le_divisor_sum
    (χ : OAI.SevenEighths.HeckeFamily.Character) (M T : ℕ) :
    (∑ m∈Finset.Icc 1 M, ∑ n∈Finset.Icc 1 T,
      ‖idealThetaCoeff χ (m*n+1)‖^2) ≤
    ∑ k∈Finset.Icc 2 (M*T+1), ((k-1).divisors.card : ℝ)*(k.divisors.card : ℝ)^2 := by
  apply (shiftedProduct_sum_le_divisors M T
    (fun k => ‖idealThetaCoeff χ k‖^2) (fun _ => sq_nonneg _)).trans
  apply Finset.sum_le_sum
  intro k _hk
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (idealThetaCoeff_norm_le_divisors_card χ k) 2)
    (Nat.cast_nonneg _)

theorem idealTheta_diagonal_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (M T : ℕ),
      (∑ m∈Finset.Icc 1 M, ∑ n∈Finset.Icc 1 T,
        ‖idealThetaCoeff χ (m*n+1)‖^2) ≤
      C*((M*T+1 : ℕ) : ℝ)^(1+ε) := by
  obtain ⟨C,hC,hbound⟩ := shiftedDiagonal_divisor_bound ε hε
  exact ⟨C,hC,fun χ M T => (idealTheta_diagonal_le_divisor_sum χ M T).trans (hbound M T)⟩

end ArtinMatthews
