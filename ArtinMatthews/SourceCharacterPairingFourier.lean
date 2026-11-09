module

public import ArtinMatthews.GiantCharacterGraph


set_option backward.privateInPublic true
@[expose] public section

/-! Conjugate difference multipliers use the original finite Fourier
coefficients and two endpoint phases of modulus one. -/
namespace ArtinMatthews
open scoped BigOperators ComplexConjugate
noncomputable section

def giantCharacterEndpointPhase {M : ℕ} [NeZero M] (r : ZMod M) (n : ℕ) : ℂ :=
  ZMod.stdAddChar (r*(n:ZMod M))

theorem giant_character_endpoint_phase_norms {M : ℕ} [NeZero M]
    (r : ZMod M) (n : ℕ) (z : ℂ) :
    ‖giantCharacterEndpointPhase r n*z‖ = ‖z‖ ∧
      ‖conj (giantCharacterEndpointPhase r n)*z‖ = ‖z‖ := by
  simp only [giantCharacterEndpointPhase,norm_mul,Complex.norm_conj,
    giant_stdAddChar_norm,one_mul,and_self]

theorem giant_character_conj_difference_expansion {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (x y : ZMod M) :
    conj (χ (y-x)) = ∑ r : ZMod M, conj (giantCharacterAdditiveCoefficient χ r)*
      ZMod.stdAddChar (r*x)*conj (ZMod.stdAddChar (r*y)) := by
  rw [giant_character_difference_expansion]
  simp only [map_sum,map_mul,starRingEnd_apply,star_star]

theorem giant_character_conj_additive_l1_le {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) :
    (∑ r : ZMod M, ‖conj (giantCharacterAdditiveCoefficient χ r)‖) ≤ (M:ℝ) := by
  simpa only [Complex.norm_conj] using giant_character_additive_l1_le χ

theorem giant_character_conj_nat_difference_expansion {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (n n' : ℕ) (h : n ≤ n') :
    conj (χ (n'-n:ℕ)) = ∑ r : ZMod M, conj (giantCharacterAdditiveCoefficient χ r)*
      giantCharacterEndpointPhase r n*conj (giantCharacterEndpointPhase r n') := by
  rw [Nat.cast_sub h]
  exact giant_character_conj_difference_expansion χ (n:ZMod M) (n':ZMod M)

/-- The reversed-order case keeps the actual value at truncated difference zero. -/
theorem giant_character_conj_nat_difference_expansion_all {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (n n' : ℕ) :
    conj (χ (n'-n:ℕ)) = if n ≤ n' then
      ∑ r : ZMod M, conj (giantCharacterAdditiveCoefficient χ r)*
        giantCharacterEndpointPhase r n*conj (giantCharacterEndpointPhase r n')
      else conj (χ 0) := by
  by_cases h : n ≤ n'
  · rw [if_pos h]
    exact giant_character_conj_nat_difference_expansion χ n n' h
  · rw [if_neg h,Nat.sub_eq_zero_of_le (le_of_not_ge h),Nat.cast_zero]

end
end ArtinMatthews
