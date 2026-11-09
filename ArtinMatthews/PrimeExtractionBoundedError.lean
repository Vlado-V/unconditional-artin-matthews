module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Filter
open scoped Asymptotics Topology

theorem prime_extraction_bounded_isLittleO (F : ℝ → ℂ) {C : ℝ}
    (hF : ∀ᶠ x : ℝ in atTop, ‖F x‖ ≤ C) (A : ℝ) :
    F =o[atTop] (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  have hb : F =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    Asymptotics.IsBigO.of_bound C (hF.mono (fun x hx => by simpa only [norm_one, mul_one] using hx))
  apply hb.trans_isLittleO
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact fun h => (mul_pos (by linarith : 0 < x)
      (Real.rpow_pos_of_pos (Real.log_pos hx) (-A))).ne' h |>.elim
  · have hlim := (isLittleO_log_rpow_rpow_atTop A (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
    simp only [Real.rpow_one] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [Real.rpow_neg (Real.log_pos hx).le]
    field_simp

end ArtinMatthews
