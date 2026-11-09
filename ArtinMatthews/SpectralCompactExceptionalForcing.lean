module

public import ArtinMatthews.SpectralExceptionalPowerForcing


set_option backward.privateInPublic true
@[expose] public section

/-! The compact same-cusp Weil bound forces the complementary exponent
at most one quarter, with constants fixed only after the frequency. -/
namespace ArtinMatthews

theorem spectral_compact_exceptional_growth_forces_quarter {κ W q : ℝ}
    (hW : 0 < W) (hq : 0 < q)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∃ D : ℝ, 0 ≤ D ∧
      ∀ A : ℝ, 0 < A → 2 * A ≤ 1 →
        A ^ (-2 * κ) * W ≤ 1 + D * (q / A)^ε * Real.sqrt (q / A)) :
    κ ≤ 1 / 4 := by
  by_contra! hk
  let ε := min (κ - 1 / 4) (1 / 4)
  have hε : 0 < ε := lt_min (sub_pos.mpr hk) (by norm_num)
  obtain ⟨D, hD₀, hD⟩ := h ε hε (min_le_right _ _)
  let β := ε + 1 / 2
  let K := D * (2 * q)^β
  let W' := (1 / 2 : ℝ)^(-(2*κ)) * W
  have hβ : 0 < β := by dsimp [β]; linarith
  have hW' : 0 < W' := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hW
  have he : 2*κ ≤ β := spectral_small_scale_exponent_le hW' (C := 1+K) (by
    intro a ha ha₁
    have ha₂ : 0 < a / 2 := by positivity
    have hh := hD (a / 2) ha₂ (by linarith)
    have hL : (a/2)^(-2*κ) * W = a^(-(2*κ)) * W' := by
      rw [show a/2 = a*(1/2) by ring, show -2*κ = -(2*κ) by ring,
        Real.mul_rpow ha.le (by norm_num : (0 : ℝ) ≤ 1/2)]
      exact mul_assoc _ _ _
    have hQ : q / (a/2) = (2*q)*a⁻¹ := by
      field_simp [ha.ne']
    have hR : D * (q/(a/2))^ε * Real.sqrt (q/(a/2)) = K * a^(-β) := by
      rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add (div_pos hq ha₂)]
      change D * (q/(a/2))^β = K * a^(-β)
      rw [hQ, Real.mul_rpow (by positivity : 0 ≤ 2*q) (inv_nonneg.mpr ha.le),
        ← Real.rpow_neg_eq_inv_rpow]
      exact (mul_assoc _ _ _).symm
    rw [hL, hR] at hh
    refine hh.trans ?_
    calc
      _ ≤ a^(-β) + K*a^(-β) := add_le_add_left
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha₁ (neg_nonpos.mpr hβ.le)) _
      _ = _ := by ring)
  have hεle : ε ≤ κ - 1 / 4 := min_le_left _ _
  dsimp only [β] at he
  linarith

end ArtinMatthews
