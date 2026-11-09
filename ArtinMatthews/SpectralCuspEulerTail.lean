module

public import ArtinMatthews.SpectralCuspEulerSolutions
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Filter
noncomputable section

theorem cuspEuler_power_energy (A : ℂ) (r : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖A*((y^r:ℝ):ℂ)‖^2/y^2 = ‖A‖^2*y^(2*r-2) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hy r),mul_pow]
  simp only [Real.rpow_sub hy,mul_comm (2:ℝ) r,Real.rpow_mul hy.le,Real.rpow_two]
  ring

theorem cuspEuler_power_energy_integrable (A : ℂ) {q : ℝ} (hq : q < 1/2) :
    IntegrableOn (fun y : ℝ => ‖A*((y^q:ℝ):ℂ)‖^2/y^2) (Ioi 1) := by
  have H := (integrableOn_Ioi_rpow_of_lt (by linarith : 2*q-2 < -1)
    (by norm_num : (0:ℝ)<1)).const_mul (‖A‖^2)
  apply H.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (cuspEuler_power_energy A q (zero_lt_one.trans hy)).symm

theorem cuspEuler_power_energy_add_bound (A B : ℂ) (p q : ℝ) {y : ℝ} (_hy : 0 < y) :
    ‖A*((y^p:ℝ):ℂ)‖^2/y^2 ≤
      2*(‖A*((y^p:ℝ):ℂ)+B*((y^q:ℝ):ℂ)‖^2/y^2)+2*(‖B*((y^q:ℝ):ℂ)‖^2/y^2) := by
  have hn := norm_sub_le (A*((y^p:ℝ):ℂ)+B*((y^q:ℝ):ℂ)) (B*((y^q:ℝ):ℂ))
  rw [add_sub_cancel_right] at hn
  have hs : ‖A*((y^p:ℝ):ℂ)‖^2 ≤
      2*‖A*((y^p:ℝ):ℂ)+B*((y^q:ℝ):ℂ)‖^2+2*‖B*((y^q:ℝ):ℂ)‖^2 := by
    nlinarith [norm_nonneg (A*((y^p:ℝ):ℂ)),norm_nonneg (B*((y^q:ℝ):ℂ)),
      norm_nonneg (A*((y^p:ℝ):ℂ)+B*((y^q:ℝ):ℂ)),
      sq_nonneg (‖A*((y^p:ℝ):ℂ)+B*((y^q:ℝ):ℂ)‖-‖B*((y^q:ℝ):ℂ)‖)]
  have h := div_le_div_of_nonneg_right hs (sq_nonneg y)
  convert h using 1
  ring

/-- Square-integrability at the actual cusp removes the growing Euler mode. -/
theorem cuspEuler_tail_forces_plus_zero (A B : ℂ) {p q : ℝ}
    (hp : 1/2 ≤ p) (hq : q < 1/2)
    (htail : IntegrableOn (fun y : ℝ =>
      ‖A*((y^p:ℝ):ℂ)+B*((y^q:ℝ):ℂ)‖^2/y^2) (Ioi 1)) : A=0 := by
  by_contra hA
  have hminus := cuspEuler_power_energy_integrable B hq
  have hbound := (htail.const_mul 2).add (hminus.const_mul 2)
  have hplus : IntegrableOn (fun y : ℝ => ‖A‖^2*y^(2*p-2)) (Ioi 1) := by
    apply hbound.mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hyp : 0 < y := zero_lt_one.trans hy
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hyp.le _)),
        ← cuspEuler_power_energy A p hyp]
      exact cuspEuler_power_energy_add_bound A B p q hyp
  have hA2 : IsUnit (‖A‖^2) := isUnit_iff_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hA))
  have hpower := (integrable_const_mul_iff hA2 (fun y : ℝ => y^(2*p-2))).mp hplus
  have hh := (integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ)<1)).mp hpower
  linarith

end
end ArtinMatthews
