module

public import ArtinMatthews.CircleNormalizerDefinitions
public import ArtinMatthews.CircleDetector


set_option backward.privateInPublic true
@[expose] public section

/-! The actual all-moduli family has linear weight mass. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem circleModuli_card_le (F r L : ℕ) :
    (circleModuli F r L).card ≤ 3 * L + 1 := by
  apply (Finset.card_filter_le _ _).trans
  rw [Nat.card_Icc]
  omega

theorem circleModuli_card_le_four (F r L : ℕ) (hL : 1 ≤ L) :
    (circleModuli F r L).card ≤ 4 * L := by
  have h := circleModuli_card_le F r L
  omega

theorem circleModuli_weightMass_le (F r L : ℕ) (hL : 1 ≤ L)
    (ω : ℕ → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hω : ∀ q ∈ circleModuli F r L, ω q ≤ W) :
    circleWeightMass (circleModuli F r L) ω ≤ 4 * W * L := by
  unfold circleWeightMass
  calc
    _ ≤ ∑ _q ∈ circleModuli F r L, W := Finset.sum_le_sum hω
    _ = ((circleModuli F r L).card : ℝ) * W := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * L : ℕ) * W :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast circleModuli_card_le_four F r L hL) hW
    _ = _ := by push_cast; ring

end ArtinMatthews
