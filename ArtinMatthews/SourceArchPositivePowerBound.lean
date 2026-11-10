module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet

theorem sourceArch_positive_power_comparison {x y C B σ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hC : 1 ≤ C)
    (hxy : x ≤ C*y) (hyx : y ≤ C*x) (hσ : |σ| ≤ B) :
    x^σ ≤ C^B*y^σ := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hu : Real.log x - Real.log y ≤ Real.log C := by
    have h := Real.log_le_log hx hxy
    rw [Real.log_mul hCpos.ne' hy.ne'] at h
    linarith
  have hl : -Real.log C ≤ Real.log x - Real.log y := by
    have h := Real.log_le_log hy hyx
    rw [Real.log_mul hCpos.ne' hx.ne'] at h
    linarith
  have hprod : σ*(Real.log x-Real.log y) ≤ B*Real.log C := by
    calc
      _ ≤ |σ*(Real.log x-Real.log y)| := le_abs_self _
      _ = |σ| * |Real.log x-Real.log y| := abs_mul _ _
      _ ≤ B*Real.log C :=
        mul_le_mul hσ (abs_le.mpr ⟨hl,hu⟩) (abs_nonneg _) ((abs_nonneg σ).trans hσ)
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hCpos, Real.rpow_def_of_pos hy,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hprod]

end ArtinMatthews.SourceArchJacquet
