module

public import ArtinMatthews.SpectralCuspEulerTail


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted L2 on an actual infinite cusp tail removes the complex Euler
power whose real part is at least one half. -/
namespace ArtinMatthews
noncomputable section
open MeasureTheory Set Filter

theorem cuspComplexEuler_power_energy (A r : ℂ) {y : ℝ} (hy : 0<y) :
    ‖A*(y:ℂ)^r‖^2/y^2=‖A‖^2*y^(2*r.re-2) := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,mul_pow]
  simp only [Real.rpow_sub hy,mul_comm (2:ℝ) r.re,Real.rpow_mul hy.le,Real.rpow_two]
  ring

theorem cuspComplexEuler_power_energy_integrable (A : ℂ) {Y : ℝ} (hY : 0<Y)
    {q : ℂ} (hq : q.re<1/2) :
    IntegrableOn (fun y : ℝ => ‖A*(y:ℂ)^q‖^2/y^2) (Ioi Y) := by
  have H := (integrableOn_Ioi_rpow_of_lt (by linarith : 2*q.re-2 < -1) hY).const_mul (‖A‖^2)
  apply H.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (cuspComplexEuler_power_energy A q (hY.trans hy)).symm

theorem cuspComplexEuler_power_energy_add_bound (A B p q : ℂ) (y : ℝ) :
    ‖A*(y:ℂ)^p‖^2/y^2 ≤ 2*(‖A*(y:ℂ)^p+B*(y:ℂ)^q‖^2/y^2)+
      2*(‖B*(y:ℂ)^q‖^2/y^2) := by
  have hn := norm_sub_le (A*(y:ℂ)^p+B*(y:ℂ)^q) (B*(y:ℂ)^q)
  rw [add_sub_cancel_right] at hn
  have hs : ‖A*(y:ℂ)^p‖^2 ≤ 2*‖A*(y:ℂ)^p+B*(y:ℂ)^q‖^2+2*‖B*(y:ℂ)^q‖^2 := by
    nlinarith [norm_nonneg (A*(y:ℂ)^p),norm_nonneg (B*(y:ℂ)^q),
      norm_nonneg (A*(y:ℂ)^p+B*(y:ℂ)^q),
      sq_nonneg (‖A*(y:ℂ)^p+B*(y:ℂ)^q‖-‖B*(y:ℂ)^q‖)]
  have h := div_le_div_of_nonneg_right hs (sq_nonneg y)
  convert h using 1
  ring

theorem cuspComplexEuler_tail_forces_plus_zero (A B p q : ℂ) {Y : ℝ}
    (hY : 0<Y) (hp : 1/2≤p.re) (hq : q.re<1/2)
    (htail : IntegrableOn (fun y : ℝ => ‖A*(y:ℂ)^p+B*(y:ℂ)^q‖^2/y^2) (Ioi Y)) : A=0 := by
  by_contra hA
  have hminus := cuspComplexEuler_power_energy_integrable B hY hq
  have hbound := (htail.const_mul 2).add (hminus.const_mul 2)
  have hplus : IntegrableOn (fun y : ℝ => ‖A‖^2*y^(2*p.re-2)) (Ioi Y) := by
    apply hbound.mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hyp := hY.trans hy
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hyp.le _)),
        ← cuspComplexEuler_power_energy A p hyp]
      exact cuspComplexEuler_power_energy_add_bound A B p q y
  have hA2 : IsUnit (‖A‖^2) := isUnit_iff_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr hA))
  have hpower := (integrable_const_mul_iff hA2 (fun y : ℝ => y^(2*p.re-2))).mp hplus
  have hh := (integrableOn_Ioi_rpow_iff hY).mp hpower
  linarith

end
end ArtinMatthews
