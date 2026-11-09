module

public import ArtinMatthews.FixedURootPowerSaving


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute reciprocal-coordinate mass errors fit inside the actual root
power-saving scale. -/
namespace ArtinMatthews

/-- Both coordinate scales above `x^δ` dominate the bounded mass shift. -/
theorem fixedURoot_volume_power_ge_one {δ x U V : ℝ} (hδ : 0 < δ) (hx : 1 ≤ x)
    (hU : x^δ ≤ U) (hV : x^δ ≤ V) :
    1 ≤ U*V*x^(-δ/1000) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hUpos : 0 < U := (Real.rpow_pos_of_pos hxpos δ).trans_le hU
  calc
    1 ≤ x^(δ+δ-δ/1000) := Real.one_le_rpow hx (by linarith)
    _ = x^δ*x^δ*x^(-δ/1000) := by
      rw [show δ+δ-δ/1000 = (δ+δ)+(-δ/1000) by ring,
        Real.rpow_add hxpos,Real.rpow_add hxpos]
    _ ≤ U*V*x^(-δ/1000) := mul_le_mul_of_nonneg_right
      (mul_le_mul hU hV (Real.rpow_nonneg hxpos.le _) hUpos.le)
      (Real.rpow_nonneg hxpos.le _)

/-- The same absorption statement in the reciprocal `V≤U` regime. -/
theorem fixedURoot_reciprocal_error_scale_one_le {δ x U V : ℝ}
    (hδ : 0 < δ) (hx : 1 < x) (hV : x^δ ≤ V) (hVU : V ≤ U) :
    1 ≤ U*V*x^(-δ/1000) :=
  fixedURoot_volume_power_ge_one hδ hx.le (hV.trans hVU) hV

end ArtinMatthews
