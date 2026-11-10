module

public import ArtinMatthews.SpectralJRegularizerLimit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

/-! The actual exponential regularizer has a uniform error above a positive gap. -/
namespace ArtinMatthews
open Set Filter
open scoped Topology
noncomputable section

theorem spectralJRegularizationMultiplier_error_le {L l δ : ℝ}
    (hL : 0 ≤ L) (hl : δ ≤ l) :
    |spectralJRegularizationMultiplier L l - 1| ≤ Real.exp (-(L * δ)) := by
  rw [spectralJRegularizationMultiplier, sub_sub_cancel_left, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hl hL))

theorem spectralJRegularizationMultiplier_gap_error_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun L : ℝ => Real.exp (-(L * δ))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hδ)

theorem spectralJRegularizationMultiplier_mul_error_le {L l δ : ℝ}
    (hL : 0 ≤ L) (hl : δ ≤ l) (z : ℂ) :
    ‖(spectralJRegularizationMultiplier L l : ℂ) * z - z‖ ≤
      Real.exp (-(L * δ)) * ‖z‖ := by
  have he : (spectralJRegularizationMultiplier L l : ℂ) * z - z =
      ((spectralJRegularizationMultiplier L l - 1 : ℝ) : ℂ) * z := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (spectralJRegularizationMultiplier_error_le hL hl) (norm_nonneg _)

theorem spectralJRegularizationMultiplier_mul_norm_le {L l : ℝ}
    (hL : 0 ≤ L) (hl : 0 ≤ l) (z : ℂ) :
    ‖(spectralJRegularizationMultiplier L l : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (spectralJRegularizationMultiplier_bounds hL hl).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (spectralJRegularizationMultiplier_bounds hL hl).2

end
end ArtinMatthews
