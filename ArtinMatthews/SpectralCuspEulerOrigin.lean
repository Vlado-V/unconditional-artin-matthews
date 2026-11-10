module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralCuspEulerTail
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped Interval
noncomputable section

theorem cuspEuler_power_energy_integral (B : ℂ) {q Y : ℝ} (hq : q < 1/2)
    (hY : 0 < Y) (hY1 : Y ≤ 1) :
    (∫ y in Icc Y 1, ‖B*((y^q:ℝ):ℂ)‖^2/y^2) =
      ‖B‖^2*((Y^(2*q-1)-1)/(1-2*q)) := by
  have he : (∫ y in Icc Y 1, ‖B*((y^q:ℝ):ℂ)‖^2/y^2) =
      ‖B‖^2*(∫ y in Icc Y 1, y^(2*q-2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    exact cuspEuler_power_energy B q (hY.trans_le hy.1)
  rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hY1,
    integral_rpow]
  · rw [Real.one_rpow]
    have hq0 : 1-2*q ≠ 0 := by linarith
    have hq1 : 2*q-2+1 ≠ 0 := by linarith
    have hexp : 2*q-2+1 = 2*q-1 := by ring
    rw [hexp]
    have hq2 : 2*q-1 ≠ 0 := by linarith
    field_simp [hq0,hq2]
    ring
  · right
    refine ⟨by linarith,?_⟩
    rw [uIcc_of_le hY1]
    intro h
    exact (not_le_of_gt hY) h.1

theorem cuspEuler_origin_power_bound (B : ℂ) {q C k : ℝ} (hk : 0 ≤ k) (hq : k+2*q < 1)
    (hnear : ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
      (∫ y in Icc Y 1, ‖B*((y^q:ℝ):ℂ)‖^2/y^2) ≤ C*Y^(-k))
    {T : ℝ} (hT : 1 ≤ T) :
    ‖B‖^2*T^(1-2*q-k) ≤ ‖B‖^2+C*(1-2*q) := by
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hTinv : 0 < T⁻¹ := inv_pos.mpr hTp
  have hTinv1 : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT
  have H := hnear T⁻¹ hTinv hTinv1
  rw [cuspEuler_power_energy_integral B (by linarith) hTinv hTinv1] at H
  have he₁ : (T⁻¹)^(2*q-1) = T^(1-2*q) := by
    rw [Real.inv_rpow hTp.le,← Real.rpow_neg hTp.le]
    congr 1
    ring
  have he₂ : (T⁻¹)^(-k) = T^k := by
    rw [Real.inv_rpow hTp.le,Real.rpow_neg hTp.le,inv_inv]
  rw [he₁,he₂] at H
  have hd : 0 < 1-2*q := by linarith
  have H' : ‖B‖^2*(T^(1-2*q)-1) ≤ C*T^k*(1-2*q) := by
    have hh := (div_le_iff₀ hd).mp (show (‖B‖^2*(T^(1-2*q)-1))/(1-2*q) ≤ C*T^k by
      simpa only [mul_div_assoc] using H)
    exact hh
  have he : T^(1-2*q) = T^k*T^(1-2*q-k) := by
    rw [← Real.rpow_add hTp]
    congr 1
    ring
  rw [he] at H'
  have hT2 : 1 ≤ T^k := Real.one_le_rpow hT hk
  have hnonneg : 0 ≤ ‖B‖^2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hT2 hnonneg,
    Real.rpow_pos_of_pos hTp k]

/-- The quantitative near-zero bound rules out the second Euler mode. -/
theorem cuspEuler_origin_forces_minus_zero (B : ℂ) {q C k : ℝ} (hk : 0 ≤ k) (hq : k+2*q < 1)
    (hnear : ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
      (∫ y in Icc Y 1, ‖B*((y^q:ℝ):ℂ)‖^2/y^2) ≤ C*Y^(-k)) : B=0 := by
  by_contra hB
  have hB2 : 0 < ‖B‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hB)
  have hr : 0 < 1-2*q-k := by linarith
  have hlim := (tendsto_rpow_atTop hr).eventually
    (eventually_gt_atTop ((‖B‖^2+C*(1-2*q))/‖B‖^2))
  obtain ⟨T,hpow,hT⟩ := (hlim.and (eventually_ge_atTop (1:ℝ))).exists
  have H := cuspEuler_origin_power_bound B hk hq hnear hT
  have H' := (div_lt_iff₀ hB2).mp hpow
  nlinarith

end
end ArtinMatthews
