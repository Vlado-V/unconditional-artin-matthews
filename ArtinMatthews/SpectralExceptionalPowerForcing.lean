module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum


set_option backward.privateInPublic true
@[expose] public section

/-! The exponent comparison for a positive exceptional Fourier term.
The upper constant can depend on the level, frequency and epsilon. -/
namespace ArtinMatthews
open Filter
open scoped Topology

theorem spectral_small_scale_exponent_le {α β A C : ℝ} (hA : 0 < A)
    (h : ∀ a : ℝ, 0 < a → a ≤ 1 → a ^ (-α) * A ≤ C * a ^ (-β)) : α ≤ β := by
  by_contra! hα
  let r := α - β
  have hr : 0 < r := sub_pos.mpr hα
  have he : ∀ᶠ x : ℝ in atTop, C / A + 1 ≤ x ^ r :=
    (tendsto_atTop.1 (tendsto_rpow_atTop hr)) _
  obtain ⟨x, hx, hxlarge⟩ := ((eventually_ge_atTop (1 : ℝ)).and he).exists
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxinv : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have hbound := h x⁻¹ (inv_pos.mpr hx0) hxinv
  simp only [Real.inv_rpow hx0.le, Real.rpow_neg hx0.le, inv_inv] at hbound
  have hp : 0 < x ^ β := Real.rpow_pos_of_pos hx0 _
  have hmul : (x ^ r * A) * x ^ β ≤ C * x ^ β := by
    calc
      _ = (x ^ r * x ^ β) * A := by ac_rfl
      _ = x ^ α * A := by rw [← Real.rpow_add hx0, show r + β = α by dsimp [r]; ring]
      _ ≤ _ := hbound
  have hle := (mul_le_mul_iff_of_pos_right hp).mp hmul
  have hlt : C < (C / A + 1) * A := by
    rw [add_mul, div_mul_cancel₀ _ hA.ne', one_mul]
    linarith
  exact (not_lt_of_ge hle) (hlt.trans_le (mul_le_mul_of_nonneg_right hxlarge hA.le))

theorem spectralABLExceptional_growth_forces_quarter {κ A : ℝ} (hA : 0 < A)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 < a → a ≤ 1 → a ^ (-4 * κ) * A ≤ C * a ^ (-1 - 2 * ε)) :
    κ ≤ 1 / 4 := by
  by_contra! hk
  let ε := min (κ - 1 / 4) (1 / 4)
  have hε : 0 < ε := lt_min (sub_pos.mpr hk) (by norm_num)
  obtain ⟨C, _, hC⟩ := h ε hε (min_le_right _ _)
  have he : 4 * κ ≤ 1 + 2 * ε := spectral_small_scale_exponent_le hA (C := C) (by
    intro a ha ha₁
    simpa only [neg_mul, neg_add_rev, sub_eq_add_neg, add_comm] using hC a ha ha₁)
  have hεle : ε ≤ κ - 1 / 4 := min_le_left _ _
  linarith

theorem spectralABLExceptional_eigenvalue_ge_three_sixteenths {eig A : ℝ}
    (heig : eig ≤ 1 / 4) (hA : 0 < A)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 < a → a ≤ 1 →
        a ^ (-4 * Real.sqrt (1 / 4 - eig)) * A ≤ C * a ^ (-1 - 2 * ε)) :
    3 / 16 ≤ eig := by
  have hκ := spectralABLExceptional_growth_forces_quarter hA h
  have hκsq := (sq_le_sq₀ (Real.sqrt_nonneg (1 / 4 - eig)) (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hκ
  rw [Real.sq_sqrt (sub_nonneg.mpr heig)] at hκsq
  linarith

end ArtinMatthews
