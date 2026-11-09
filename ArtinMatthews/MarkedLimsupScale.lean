module

public import ArtinMatthews.MarkedDeweightingParameter
public import Mathlib.Order.LiminfLimsup


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Filter
open scoped Topology

/-- Normalize an eventual `x/log x` bound and take its real limsup. -/
theorem marked_normalized_limsup_le (E : ℝ → ℝ) (B : ℝ)
    (hE : ∀ᶠ x : ℝ in atTop, 0 ≤ E x)
    (hB : ∀ᶠ x : ℝ in atTop, E x ≤ B * x / Real.log x) :
    limsup (fun x => Real.log x / x * E x) atTop ≤ B := by
  have hnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log x / x * E x := by
    filter_upwards [hE, eventually_gt_atTop (1 : ℝ)] with x hE hx
    exact mul_nonneg (div_nonneg (Real.log_pos hx).le (by linarith)) hE
  apply limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hnonneg)
  filter_upwards [hB, eventually_gt_atTop (1 : ℝ)] with x hB hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  calc
    Real.log x / x * E x ≤ Real.log x / x * (B * x / Real.log x) :=
      mul_le_mul_of_nonneg_left hB (div_nonneg hlog.le hx0.le)
    _ = B := by field_simp

end ArtinMatthews
