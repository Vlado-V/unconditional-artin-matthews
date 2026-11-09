module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source conductor dominates the exceptional moment scale. -/
namespace ArtinMatthews
noncomputable section

theorem spectralABL_source_conductor_power
    {Q R Z n r F X ε : ℝ}
    (hF : 1 ≤ F) (hr : 1 ≤ r) (hn : 1 ≤ n) (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hQ : F ≤ Q) (hX : 0 < X) (hε : 0 ≤ ε)
    (hInv : X⁻¹ ≤ Q*R*Z*n*r) :
    (r*F*n/(X/Z))^ε ≤ (Q*R*Z*n*r)^(3*ε) := by
  let P := Q*R*Z*n*r
  have hFR : F ≤ Q*R := hQ.trans (le_mul_of_one_le_right
    (zero_le_one.trans (hF.trans hQ)) hR)
  have hsmall : r*F*n*Z ≤ P := by
    have hs := mul_le_mul_of_nonneg_right hFR (by positivity : 0 ≤ Z*n*r)
    convert hs using 1 <;> ring
  have hsmall₁ : 1 ≤ r*F*n*Z :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr hF) hn) hZ
  have hP₁ : 1 ≤ P := hsmall₁.trans hsmall
  have hP₀ : 0 ≤ P := zero_le_one.trans hP₁
  have hZ₀ : 0 < Z := zero_lt_one.trans_le hZ
  have hT : r*F*n/(X/Z) ≤ P^3 := by
    calc
      _ = (r*F*n*Z)*X⁻¹ := by field_simp [hX.ne',hZ₀.ne']
      _ ≤ P*P := mul_le_mul hsmall hInv (inv_nonneg.mpr hX.le) hP₀
      _ = P^2 := by ring
      _ ≤ P^2*P := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hP₁ (sq_nonneg P)
      _ = _ := by ring
  calc
    _ ≤ (P^3)^ε := Real.rpow_le_rpow (by positivity) hT hε
    _ = P^(3*ε) := (Real.rpow_natCast_mul hP₀ 3 ε).symm

end
end ArtinMatthews
