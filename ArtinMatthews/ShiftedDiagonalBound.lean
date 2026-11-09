module

public import ArtinMatthews.ShiftedDiagonalFiber
public import OAI.NumberTheory.Jacobsthal.Sieve.DivisorLogGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Subpower diagonal bound after exact product-fiber counting. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem shiftedDiagonal_divisor_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ M T : ℕ,
      (∑ k∈Finset.Icc 2 (M*T+1),
        ((k-1).divisors.card : ℝ)*(k.divisors.card : ℝ)^2) ≤
      C*((M*T+1 : ℕ) : ℝ)^(1+ε) := by
  obtain ⟨C₁,hC₁,h₁⟩ := OAI.Erdos970.ErdosDivisorBounds.divisor_power_subpower 1
    (show 0<ε/2 by linarith)
  obtain ⟨C₂,hC₂,h₂⟩ := OAI.Erdos970.ErdosDivisorBounds.divisor_power_subpower 2
    (show 0<ε/2 by linarith)
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro M T
  let X : ℕ := M*T+1
  have hX : (0 : ℝ)<X := by dsimp [X]; positivity
  have hpoint : ∀ k∈Finset.Icc 2 X,
      ((k-1).divisors.card : ℝ)*(k.divisors.card : ℝ)^2 ≤
        (C₁*C₂)*(X : ℝ)^ε := by
    intro k hk
    obtain ⟨hk₂,hkX⟩ := Finset.mem_Icc.mp hk
    have hkm : k-1≤X := (Nat.sub_le k 1).trans hkX
    have hfirst : ((k-1).divisors.card : ℝ) ≤ C₁*(X : ℝ)^(ε/2) := by
      have h := h₁ (k-1) (by omega)
      simp only [pow_one] at h
      exact h.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkm) (by positivity)) hC₁.le)
    have hsecond : (k.divisors.card : ℝ)^2 ≤ C₂*(X : ℝ)^(ε/2) :=
      (h₂ k (by omega)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hkX) (by positivity)) hC₂.le)
    calc
      _ ≤ (C₁*(X : ℝ)^(ε/2))*(C₂*(X : ℝ)^(ε/2)) :=
        mul_le_mul hfirst hsecond (sq_nonneg _) (by positivity)
      _ = (C₁*C₂)*(X : ℝ)^ε := by
        rw [show ε=ε/2+ε/2 by ring,Real.rpow_add hX]
        ring
  have hcard : ((Finset.Icc 2 X).card : ℝ)≤X := by
    exact_mod_cast (show (Finset.Icc 2 X).card≤X by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ _k∈Finset.Icc 2 X, (C₁*C₂)*(X : ℝ)^ε :=
      Finset.sum_le_sum hpoint
    _ = ((Finset.Icc 2 X).card : ℝ)*((C₁*C₂)*(X : ℝ)^ε) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (X : ℝ)*((C₁*C₂)*(X : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (C₁*C₂)*(X : ℝ)^(1+ε) := by rw [Real.rpow_add hX,Real.rpow_one]; ring

/-- A general coefficient-sequence consequence, ready to specialize only
after its actual divisor majorant has been proved. -/
theorem shiftedDiagonal_norm_bound (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖≤(n.divisors.card : ℝ)) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ M T : ℕ,
      (∑ m∈Finset.Icc 1 M, ∑ n∈Finset.Icc 1 T, ‖a (m*n+1)‖^2) ≤
      C*((M*T+1 : ℕ) : ℝ)^(1+ε) := by
  obtain ⟨C,hC,hbound⟩ := shiftedDiagonal_divisor_bound ε hε
  refine ⟨C,hC,?_⟩
  intro M T
  apply (shiftedProduct_sum_le_divisors M T (fun k => ‖a k‖^2)
    (fun _ => sq_nonneg _)).trans
  apply le_trans _ (hbound M T)
  apply Finset.sum_le_sum
  intro k _hk
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ha k) 2)
    (Nat.cast_nonneg _)

end ArtinMatthews
