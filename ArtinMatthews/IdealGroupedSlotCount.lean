module

public import ArtinMatthews.IdealGroupedSelected


set_option backward.privateInPublic true
@[expose] public section

/-! The actual selected-slot carrier inherits the logarithmic group
count without replacing any ordered labels by numeric products. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators

theorem idealGroupedSlot_card_le {A : Type*} [Fintype A] (k : A → ℕ)
    (m : ℕ) (hk : ∀ i, k i ≤ m) :
    Fintype.card (Σ i, Fin (k i)) ≤ m*Fintype.card A := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∑ _i : A, m := sum_le_sum fun i _ => hk i
    _ = _ := by rw [sum_const, card_univ, smul_eq_mul, mul_comm]

theorem idealGroupedSlot_card_source {A : Type*} [Fintype A] (k : A → ℕ)
    (m : ℕ) (hk : ∀ i, k i ≤ m) {C L : ℝ}
    (hcard : (Fintype.card A : ℝ) ≤ C*Real.log L) :
    (Fintype.card (Σ i, Fin (k i)) : ℝ) ≤ ((m : ℝ)*C)*Real.log L := by
  have h := idealGroupedSlot_card_le k m hk
  calc
    _ ≤ (m : ℝ)*(Fintype.card A : ℝ) := by exact_mod_cast h
    _ ≤ (m : ℝ)*(C*Real.log L) := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
    _ = _ := by ring

end ArtinMatthews
