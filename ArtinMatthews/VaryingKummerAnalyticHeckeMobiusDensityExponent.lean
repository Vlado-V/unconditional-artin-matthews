module

public import ArtinMatthews.VaryingKummerAnalyticHeckeMobiusPowerAnnuli


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit conductor, norm-window, height and logarithmic exponents for
the actual detector. A fixed finite norm partition still leaves a strict
margin below the target exponent one half. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open Real
noncomputable section

theorem log_power_window_bound {U a : ℝ} (hU : 1 ≤ U) (ha0 : 0 ≤ a) (ha : a ≤ 11) :
    (1+(Real.log (U^a))^2)^2 ≤ (1210001 : ℝ)^2*U^(1/25 : ℝ) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hl0 := Real.log_nonneg hU
  have hl := Real.log_le_rpow_div hU0.le (by norm_num : (0 : ℝ) < 1/100)
  have hl' : Real.log U ≤ 100*U^(1/100 : ℝ) := by convert hl using 1; ring
  have hla : 0 ≤ Real.log (U^a) := by rw [Real.log_rpow hU0]; positivity
  have hla' : Real.log (U^a) ≤ 1100*U^(1/100 : ℝ) := by
    rw [Real.log_rpow hU0]
    calc
      _ ≤ 11*Real.log U := mul_le_mul_of_nonneg_right ha hl0
      _ ≤ 11*(100*U^(1/100 : ℝ)) := mul_le_mul_of_nonneg_left hl' (by norm_num)
      _ = _ := by ring
  have hp : (U^(1/100 : ℝ))^2=U^(1/50 : ℝ) := by
    rw [← Real.rpow_mul_natCast hU0.le]
    norm_num
  have hsq : (Real.log (U^a))^2 ≤ 1210000*U^(1/50 : ℝ) := by
    have H := (sq_le_sq₀ hla (by positivity)).mpr hla'
    norm_num [mul_pow,hp] at H
    exact H
  have hone : 1 ≤ U^(1/50 : ℝ) := Real.one_le_rpow hU (by norm_num)
  have hsum : 1+(Real.log (U^a))^2 ≤ 1210001*U^(1/50 : ℝ) := by linarith
  have H := (sq_le_sq₀ (by positivity) (by positivity)).mpr hsum
  have hp' : (U^(1/50 : ℝ))^2=U^(1/25 : ℝ) := by
    rw [← Real.rpow_mul_natCast hU0.le]
    norm_num
  simpa only [mul_pow,hp'] using H

theorem mobiusPowerBoundary_bounds {U : ℝ} (hU : 1 ≤ U) {j : ℕ} (hj : j < 144) :
    U^2 ≤ mobiusPowerBoundary U j ∧
      mobiusPowerBoundary U j ≤ mobiusPowerBoundary U (j+1) ∧
      mobiusPowerBoundary U (j+1) ≤ U^11 := by
  have hm := mobiusPowerBoundary_monotone hU
  rw [← (mobiusPowerBoundary_endpoints U).1,← (mobiusPowerBoundary_endpoints U).2]
  exact ⟨hm (Nat.zero_le _),hm (Nat.le_succ _),hm (by omega)⟩

theorem mobius_norm_height_log_cost {U r : ℝ} (hU : 1 ≤ U) (hr : r ≤ 1/10)
    {j : ℕ} (hj : j < 144) :
    (1+4*(4*U^r))*(mobiusPowerBoundary U (j+1)+U^2)*
      (1+(Real.log (mobiusPowerBoundary U (j+1)))^2)^2*
      (mobiusPowerBoundary U j)^(-(9917/10000 : ℝ)) ≤
        (34*(1210001 : ℝ)^2)*U^(2/5 : ℝ) := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  let a : ℝ := 2+(j : ℝ)/16
  let b : ℝ := 2+((j+1 : ℕ) : ℝ)/16
  have hj' : (j : ℝ) < 144 := by exact_mod_cast hj
  have hjle : (j : ℝ) ≤ 143 := by exact_mod_cast (show j ≤ 143 by omega)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha11 : a ≤ 11 := by dsimp [a]; linarith
  have hb11 : b ≤ 11 := by dsimp [b]; push_cast; linarith
  have hab : b=a+1/16 := by dsimp [a,b]; push_cast; ring
  have hheight : 1+4*(4*U^r) ≤ 17*U^(1/10 : ℝ) := by
    have hmono := Real.rpow_le_rpow_of_exponent_le hU hr
    have hone := Real.one_le_rpow hU (by norm_num : (0 : ℝ) ≤ 1/10)
    linarith
  have hnorm : mobiusPowerBoundary U (j+1)+U^2 ≤ 2*U^b := by
    have hbnd := (mobiusPowerBoundary_bounds hU hj)
    have hlow : U^2 ≤ U^b := hbnd.1.trans hbnd.2.1
    change U^b+U^2 ≤ 2*U^b
    linarith
  have hlog := log_power_window_bound hU hb hb11
  have hcollapse : U^(1/10 : ℝ)*U^b*U^(1/25 : ℝ)*(U^a)^(-(9917/10000 : ℝ)) =
      U^((1/10 : ℝ)+b+1/25-a*(9917/10000 : ℝ)) := by
    rw [← Real.rpow_mul hU0.le,← Real.rpow_add hU0,← Real.rpow_add hU0,← Real.rpow_add hU0]
    congr 1
    ring
  have hexp : (1/10 : ℝ)+b+1/25-a*(9917/10000 : ℝ) ≤ 2/5 := by
    rw [hab]
    linarith
  calc
    _ ≤ (17*U^(1/10 : ℝ))*(2*U^b)*((1210001 : ℝ)^2*U^(1/25 : ℝ))*
        (U^a)^(-(9917/10000 : ℝ)) := by
      change (1+4*(4*U^r))*(mobiusPowerBoundary U (j+1)+U^2)*
        (1+(Real.log (U^b))^2)^2*(U^a)^(-(9917/10000 : ℝ)) ≤ _
      gcongr
      exact add_nonneg (Real.rpow_nonneg hU0.le _) (sq_nonneg U)
    _ = (34*(1210001 : ℝ)^2)*(U^(1/10 : ℝ)*U^b*U^(1/25 : ℝ)*(U^a)^(-(9917/10000 : ℝ))) := by ring
    _ ≤ _ := by
      rw [hcollapse]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hexp) (by positivity)

end
end ArtinMatthews.VaryingKummerAnalytic
