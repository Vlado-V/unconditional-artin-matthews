module

public import ArtinMatthews.CuspAverageProjectionOperator
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Exact weighted energy of the genuine unnormalized vertical L² space. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

theorem cuspVerticalL2_integrable_density_iff {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (F : ℝ → ℝ) :
    Integrable F ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) ↔
      IntegrableOn (fun y => F y / y ^ 2) (Ioi Y) volume := by
  rw [cuspHorizontalMeasure_univ,
    integrable_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr hw)) ENNReal.ofReal_ne_top,
    cuspVerticalMeasure, integrable_withDensity_iff_integrable_smul'
      (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := hY.trans hy
  rw [ENNReal.toReal_ofReal (zpow_nonneg hypos.le (-2 : ℤ))]
  simp only [smul_eq_mul, zpow_neg, zpow_ofNat, div_eq_mul_inv]
  ring

theorem cuspVerticalL2_integral_density {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (F : ℝ → ℝ) :
    (∫ y, F y ∂((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y)) =
      w * (∫ y in Ioi Y, F y / y ^ 2) := by
  rw [cuspHorizontalMeasure_univ, integral_smul_measure, ENNReal.toReal_ofReal hw.le,
    smul_eq_mul, cuspVerticalMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := hY.trans hy
  rw [ENNReal.toReal_ofReal (zpow_nonneg hypos.le (-2 : ℤ))]
  simp only [smul_eq_mul, zpow_neg, zpow_ofNat, div_eq_mul_inv]
  ring

theorem cuspVerticalL2_integrable_energy {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (a : CuspVerticalL2 w Y) :
    IntegrableOn (fun y : ℝ => ‖a y‖ ^ 2 / y ^ 2) (Ioi Y) volume :=
  (cuspVerticalL2_integrable_density_iff hw hY _).mp
    ((Lp.memLp a).integrable_norm_pow (by norm_num))

theorem cuspVerticalL2_norm_sq_integral (w Y : ℝ) (a : CuspVerticalL2 w Y) :
    ‖a‖ ^ 2 = ∫ y, ‖a y‖ ^ 2 ∂((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem cuspVerticalL2_energy_identity {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (a : CuspVerticalL2 w Y) :
    w * (∫ y in Ioi Y, ‖a y‖ ^ 2 / y ^ 2) = ‖a‖ ^ 2 := by
  rw [cuspVerticalL2_norm_sq_integral, cuspVerticalL2_integral_density hw hY]

theorem cuspVerticalL2_energy_eq {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (a : CuspVerticalL2 w Y) :
    (∫ y in Ioi Y, ‖a y‖ ^ 2 / y ^ 2) = ‖a‖ ^ 2 / w := by
  apply (eq_div_iff hw.ne').mpr
  simpa only [mul_comm w] using cuspVerticalL2_energy_identity hw hY a

end
end ArtinMatthews
