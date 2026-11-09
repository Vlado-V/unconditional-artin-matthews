module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A scalar reciprocal-pole difference is controlled by the positive
pole weight on the line of real part two. -/

namespace OAI.PrimeDegreePackets.AnalyticGrowth

theorem norm_pole_reciprocal_difference_le {b s ρ : ℂ} {δ : ℝ}
    (hb : b.re = 2) (hρ : ρ.re ≤ 1) (hδ : 0 < δ) (hdist : δ ≤ ‖s-ρ‖) :
    ‖1/(s-ρ)-1/(b-ρ)‖ ≤
      ‖b-s‖*(1+‖b-s‖/δ)*(1/(b-ρ)).re := by
  have hvre : 1 ≤ (b-ρ).re := by simp only [Complex.sub_re]; linarith
  have hv0 : b-ρ ≠ 0 := by
    intro hh
    have hh' := congrArg Complex.re hh
    simp only [Complex.zero_re] at hh'
    linarith
  have hv : 0 < ‖b-ρ‖ := norm_pos_iff.mpr hv0
  have hu : 0 < ‖s-ρ‖ := hδ.trans_le hdist
  have hu0 : s-ρ ≠ 0 := norm_pos_iff.mp hu
  have hrecip : 1/‖b-ρ‖^2 ≤ (1/(b-ρ)).re := by
    simp only [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    simpa only [one_div] using div_le_div_of_nonneg_right hvre (sq_nonneg ‖b-ρ‖)
  have htriangle : ‖b-ρ‖ ≤ ‖s-ρ‖+‖b-s‖ := by
    calc
      _ = ‖(s-ρ)+(b-s)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hratio : ‖b-ρ‖/‖s-ρ‖ ≤ 1+‖b-s‖/δ := by
    calc
      _ ≤ (‖s-ρ‖+‖b-s‖)/‖s-ρ‖ := div_le_div_of_nonneg_right htriangle hu.le
      _ = 1+‖b-s‖/‖s-ρ‖ := by field_simp
      _ ≤ _ := by
        have hh := div_le_div_of_nonneg_left (norm_nonneg (b-s)) hδ hdist
        linarith
  have hid : 1/(s-ρ)-1/(b-ρ) = (b-s)/((s-ρ)*(b-ρ)) := by
    field_simp [hu0,hv0]
    ring
  calc
    _ = ‖b-s‖*(‖b-ρ‖/‖s-ρ‖)*(1/‖b-ρ‖^2) := by
      rw [hid, norm_div, norm_mul]
      field_simp
    _ ≤ ‖b-s‖*(1+‖b-s‖/δ)*(1/‖b-ρ‖^2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (norm_nonneg _)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hrecip (by positivity)

end OAI.PrimeDegreePackets.AnalyticGrowth
