module

public import ArtinMatthews.GiantSignedEdgeSlotBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The literal change from forward to reversed promotion charges has a
uniform factor per group for bounded numbers of free slots. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

def giantSignedEdgeReverseConstant (vmin vmax : ℝ) (tmax : ℕ) : ℝ :=
  (max 1 vmax) ^ tmax * (max 1 vmin⁻¹) ^ tmax

theorem giantSignedEdgeReverseConstant_nonneg (vmin vmax : ℝ) (tmax : ℕ) :
    0 ≤ giantSignedEdgeReverseConstant vmin vmax tmax := by
  unfold giantSignedEdgeReverseConstant
  positivity

theorem giantSignedEdgeReverseFactor_bound {J : Type*} [Fintype J]
    (V : J → ℝ) {vmin vmax : ℝ} (hvmin : 0 < vmin)
    (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    (a b : J → ℕ) (tmax : ℕ) (ha : ∀ j, a j ≤ tmax) (hb : ∀ j, b j ≤ tmax) :
    (∏ j, (V j) ^ b j / (V j) ^ a j) ≤
      (giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J := by
  classical
  calc
    _ ≤ ∏ _j : J, giantSignedEdgeReverseConstant vmin vmax tmax := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact div_nonneg (pow_nonneg (lt_of_lt_of_le hvmin (hVmin j)).le _)
          (pow_nonneg (lt_of_lt_of_le hvmin (hVmin j)).le _)
      · intro j _
        have hVp : 0 < V j := lt_of_lt_of_le hvmin (hVmin j)
        have hInv : (V j)⁻¹ ≤ vmin⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hvmin (hVmin j)
        have hB : (V j) ^ b j ≤ (max 1 vmax) ^ tmax :=
          (pow_le_pow_left₀ hVp.le ((hVmax j).trans (le_max_right _ _)) _).trans
            (pow_le_pow_right₀ (le_max_left _ _) (hb j))
        have hA : (V j)⁻¹ ^ a j ≤ (max 1 vmin⁻¹) ^ tmax :=
          (pow_le_pow_left₀ (inv_nonneg.mpr hVp.le)
            (hInv.trans (le_max_right _ _)) _).trans
            (pow_le_pow_right₀ (le_max_left _ _) (ha j))
        simp only [div_eq_mul_inv, ← inv_pow]
        exact mul_le_mul hB hA (pow_nonneg (inv_nonneg.mpr hVp.le) _) (by positivity)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end
end ArtinMatthews
