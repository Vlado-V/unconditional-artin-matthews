module

public import ArtinMatthews.GiantSignedGhostAbsoluteRow


set_option backward.privateInPublic true
@[expose] public section

/-! A single exponential memory weight controls the forward and reversed
ghost coefficients, including doubled original births. -/
namespace ArtinMatthews
noncomputable section

theorem giantSignedGhostWeight_exists (aMax cMax dMax : ℝ) (ha : aMax < 1) :
    ∃ v : ℝ, 1 < v ∧ ∀ A C D : ℝ,
      A ≤ aMax → |C| ≤ cMax → |D| ≤ dMax →
        A + |D| / v < 1 ∧ A + 2 * |C| / v < 1 := by
  let R := max dMax (2 * cMax)
  let v := max 2 ((R + 1) / (1 - aMax))
  have hv : 1 < v := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hv0 : 0 < v := lt_trans (by norm_num) hv
  have heps : 0 < 1 - aMax := sub_pos.mpr ha
  have hRv : R + 1 ≤ v * (1 - aMax) :=
    (div_le_iff₀ heps).mp (le_max_right _ _)
  have hdiv : R / v < 1 - aMax := (div_lt_iff₀ hv0).mpr (by nlinarith)
  refine ⟨v, hv, ?_⟩
  intro A C D hA hC hD
  have hDv : |D| / v ≤ R / v :=
    (div_le_div_iff_of_pos_right hv0).mpr (hD.trans (le_max_left _ _))
  have hCv : 2 * |C| / v ≤ R / v :=
    (div_le_div_iff_of_pos_right hv0).mpr
      ((mul_le_mul_of_nonneg_left hC (by norm_num)).trans (le_max_right _ _))
  constructor <;> linarith

theorem giantSignedGhost_source_A_lt_one {q ρ : ℝ} (hρ : 0 < ρ) (hq : q < ρ ^ 2) :
    q / ρ ^ 2 < 1 := by
  exact (div_lt_one (sq_pos_of_pos hρ)).mpr hq

end
end ArtinMatthews
