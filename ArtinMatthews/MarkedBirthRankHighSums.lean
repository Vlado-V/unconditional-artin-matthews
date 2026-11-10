module

public import ArtinMatthews.MarkedBirthDistinctPermutation
public import Mathlib.Basic.Real.Basic
public import ArtinMatthews.MarkedBirthRankSums


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite high-rank summation for the performed-birth permutation
expansion. The full permutation carrier and the proved rank count remain. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedBirthPermutation_rank_le_card {A : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) : markedBirthPermutationRank σ ≤ Fintype.card A := by
  unfold markedBirthPermutationRank
  rw [Equiv.Perm.sum_cycleType]
  exact (Nat.sub_le _ _).trans (Finset.card_le_univ _)

theorem markedBirthRank_high_sum_le {A : Type*} [Fintype A] [DecidableEq A]
    (r₀ : ℕ) (F : Equiv.Perm A → ℝ) {C Δ : ℝ} (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hF : ∀ σ, r₀ ≤ markedBirthPermutationRank σ → F σ ≤ C*Δ^(markedBirthPermutationRank σ)) :
    (∑ σ, if r₀ ≤ markedBirthPermutationRank σ then F σ else 0) ≤
      ∑ r ∈ Finset.range (Fintype.card A+1), if r₀ ≤ r then
        ((Fintype.card A:ℝ)^2+1)^(2*r)*C*Δ^r else 0 := by
  let G := fun σ : Equiv.Perm A => if r₀ ≤ markedBirthPermutationRank σ then F σ else 0
  let T := fun r : ℕ => if r₀ ≤ r then C*Δ^r else 0
  have hT (r : ℕ) (_hr : r < Fintype.card A+1) : 0 ≤ T r := by
    dsimp [T]
    split_ifs
    · exact mul_nonneg hC (pow_nonneg hΔ _)
    · exact le_rfl
  have hG (σ : Equiv.Perm A) (_hσ : markedBirthPermutationRank σ < Fintype.card A+1) :
      G σ ≤ T (markedBirthPermutationRank σ) := by
    dsimp [G,T]
    split_ifs with hr
    · exact hF σ hr
    · exact le_rfl
  have h := markedBirthRank_low_sum_le (Fintype.card A+1) G T hT hG
  have heq : (∑ σ, if markedBirthPermutationRank σ < Fintype.card A+1 then G σ else 0)=
      ∑ σ, if r₀ ≤ markedBirthPermutationRank σ then F σ else 0 := by
    apply Finset.sum_congr rfl
    intro σ _
    rw [ite_eq_left (Nat.lt_succ_iff.mpr (markedBirthPermutation_rank_le_card σ))]
  rw [heq] at h
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro r _
  dsimp [T]
  split_ifs <;> simp only [mul_zero,mul_assoc]

end ArtinMatthews
