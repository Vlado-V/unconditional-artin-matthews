module

public import ArtinMatthews.ShiftedABLRadialParameterBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The common dyadic radial scale also dominates the inverse of the
actual ABL conductor. No individual signed frequency enters this bound. -/

noncomputable section
namespace ArtinMatthews

theorem shiftedABLDyadicRadialParameter_inv_le_scale
    {F L n r : ℕ} {R Z : ℝ}
    (hF : 0 < F) (hL : 0 < L) (hn : 0 < n) (hr : 0 < r)
    (hR : 1 ≤ R) (hZ : 1 ≤ Z) :
    (ablTheorem24SpectralParameter (3*(L : ℝ)/(F : ℝ)) R Z n r F)⁻¹ ≤
      ablTheorem24BesselScale (3*(L : ℝ)/(F : ℝ)) R n r F := by
  let P' := ablTheorem24SpectralParameter (3*(L : ℝ)/(F : ℝ)) R Z n r F
  let X := ablTheorem24BesselScale (3*(L : ℝ)/(F : ℝ)) R n r F
  have hF0 : (F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hF.ne'
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hL0 : (0 : ℝ) < L := zero_lt_one.trans_le hL1
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans_le hr1
  have hden : 0 < Real.sqrt (r : ℝ)*(3*(L : ℝ)) := by positivity
  have hPeq : P' = (3*(L : ℝ))*R*Z*n*r := by
    dsimp [P',ablTheorem24SpectralParameter]
    field_simp [hF0]
  have hP0 : 0 < P' := by rw [hPeq]; positivity
  have hXeq : X = Real.sqrt (R*(n : ℝ))/(Real.sqrt (r : ℝ)*(3*(L : ℝ))) := by
    dsimp [X,ablTheorem24BesselScale]
    congr 1
    field_simp [hF0]
  have hsqrLe : Real.sqrt (r : ℝ) ≤ r :=
    Real.sqrt_le_iff.2 ⟨hr0.le,by nlinarith⟩
  have hnum : 1 ≤ Real.sqrt (R*(n : ℝ)) :=
    Real.one_le_sqrt.2 (one_le_mul_of_one_le_of_one_le hR hn1)
  have hdenP : Real.sqrt (r : ℝ)*(3*(L : ℝ)) ≤ P' := by
    calc
      _ ≤ (r : ℝ)*(3*(L : ℝ)) :=
        mul_le_mul_of_nonneg_right hsqrLe (by positivity)
      _ ≤ ((r : ℝ)*(3*(L : ℝ)))*(R*Z*(n : ℝ)) :=
        le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hR hZ) hn1)
      _ = P' := by rw [hPeq]; ring
  change P'⁻¹ ≤ X
  rw [← one_div,hXeq]
  apply (div_le_div_iff₀ hP0 hden).2
  calc
    _ = Real.sqrt (r : ℝ)*(3*(L : ℝ)) := by ring
    _ ≤ P' := hdenP
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnum hP0.le

end ArtinMatthews
