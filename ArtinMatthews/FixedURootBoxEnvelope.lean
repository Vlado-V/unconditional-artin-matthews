module

public import ArtinMatthews.FixedURootBoxMain


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit root-box error is bounded by the paper's coordinate-scale
error when the first scale is the smaller one. -/
namespace ArtinMatthews

/-- Uniformly over all interval parameters, the full root-box error is
`O(V*U^0.99*S²)` for `1≤U≤V`. -/
theorem fixedURootBox_error_envelope {K U V A B R Y : ℝ} {N S : ℕ}
    (hK : 0 ≤ K) (hU : 1 ≤ U) (hUV : U ≤ V) (hUA : U ≤ A)
    (hAB : A ≤ B) (hB : B ≤ 16*U) (hN : (N : ℝ) ≤ 17*U)
    (hS : 0 < S) (hR : 0 ≤ R) (hR1 : R ≤ 1) (hY : 0 ≤ Y) (hYV : Y ≤ V) :
    K * B^(99/100 : ℝ) * (S : ℝ)^2 * (2+Y/A) * ((B-A)/(S : ℝ)+1) +
      (R*Y/(S : ℝ)^2)*(2+Real.log N) ≤
      (816*K+20)*V*U^(99/100 : ℝ)*(S : ℝ)^2 := by
  have hUpos : 0 < U := by linarith
  have hApos : 0 < A := hUpos.trans_le hUA
  have hVpos : 0 < V := hUpos.trans_le hUV
  have hBpos : 0 < B := hApos.trans_le hAB
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hP : 0 < U^(99/100 : ℝ) := Real.rpow_pos_of_pos hUpos _
  have hP1 : 1 ≤ U^(99/100 : ℝ) := Real.one_le_rpow hU (by norm_num)
  have h16 : (16 : ℝ)^(99/100 : ℝ) ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤16)
      (by norm_num : (99/100:ℝ)≤1)
    simpa only [Real.rpow_one] using hh
  have hBpow : B^(99/100 : ℝ) ≤ 16*U^(99/100 : ℝ) := by
    calc
      _ ≤ (16*U)^(99/100 : ℝ) := Real.rpow_le_rpow hBpos.le hB (by norm_num)
      _ = (16 : ℝ)^(99/100 : ℝ)*U^(99/100 : ℝ) := Real.mul_rpow (by norm_num) hUpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h16 hP.le
  have hfrac : Y/A ≤ V/U :=
    (div_le_div_of_nonneg_right hYV hApos.le).trans
      (div_le_div_of_nonneg_left hVpos.le hUpos hUA)
  have hVU : 1 ≤ V/U := (one_le_div hUpos).mpr hUV
  have hfactor : 2+Y/A ≤ 3*V/U := by
    calc
      _ ≤ 2+V/U := by linarith
      _ ≤ 3*(V/U) := by linarith
      _ = _ := by ring
  have hcard : (B-A)/(S : ℝ)+1 ≤ 17*U := by
    have hh := div_le_self (sub_nonneg.mpr hAB) hS1
    linarith
  have hfirst : K * B^(99/100 : ℝ) * (S : ℝ)^2 * (2+Y/A) * ((B-A)/(S : ℝ)+1) ≤
      816*K*V*U^(99/100 : ℝ)*(S : ℝ)^2 := by
    calc
      _ ≤ K * (16*U^(99/100 : ℝ)) * (S : ℝ)^2 * (3*V/U) * (17*U) := by
        gcongr
      _ = _ := by field_simp; ring
  have h17 : (17 : ℝ)^(99/100 : ℝ) ≤ 17 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤17)
      (by norm_num : (99/100:ℝ)≤1)
    simpa only [Real.rpow_one] using hh
  have hNpow : (N : ℝ)^(99/100 : ℝ) ≤ 17*U^(99/100 : ℝ) := by
    calc
      _ ≤ (17*U)^(99/100 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by norm_num)
      _ = (17 : ℝ)^(99/100 : ℝ)*U^(99/100 : ℝ) := Real.mul_rpow (by norm_num) hUpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h17 hP.le
  have hlog := Real.log_natCast_le_rpow_div N (by norm_num : (0:ℝ)<99/100)
  have hlogBound : 2+Real.log N ≤ 20*U^(99/100 : ℝ) := by nlinarith
  have hSsq : 1 ≤ (S : ℝ)^2 := by nlinarith
  have hRY : R*Y ≤ V := by nlinarith
  have hT : R*Y/(S : ℝ)^2 ≤ V :=
    (div_le_self (mul_nonneg hR hY) hSsq).trans hRY
  have hsecond : (R*Y/(S : ℝ)^2)*(2+Real.log N) ≤
      20*V*U^(99/100 : ℝ)*(S : ℝ)^2 := by
    calc
      _ ≤ V * (20*U^(99/100 : ℝ)) := by
        apply mul_le_mul hT hlogBound
        · have hh : 0 ≤ Real.log N := Real.log_natCast_nonneg N
          linarith
        · exact hVpos.le
      _ = 20*V*U^(99/100 : ℝ) := by ring
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hSsq
          (show 0 ≤ 20*V*U^(99/100 : ℝ) by positivity)
  calc
    _ ≤ 816*K*V*U^(99/100 : ℝ)*(S : ℝ)^2 +
        20*V*U^(99/100 : ℝ)*(S : ℝ)^2 := add_le_add hfirst hsecond
    _ = _ := by ring

end ArtinMatthews
