module

public import ArtinMatthews.MarkedDeweightingScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


set_option backward.privateInPublic true
@[expose] public section

/-! The final array-count parameter in positive marked deweighting. -/

namespace ArtinMatthews

open Filter
open scoped Topology

theorem marked_deweighting_array_count_decay (C : ℝ) :
    Tendsto (fun b : ℕ => C / Real.sqrt b) atTop (𝓝 0) := by
  have h : Tendsto (fun b : ℕ => (b : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  simpa only [Real.sqrt_eq_rpow] using h.const_div_atTop C

end ArtinMatthews
