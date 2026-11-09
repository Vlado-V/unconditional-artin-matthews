module

public import ArtinMatthews.GiantTwoSidedRootIntervalBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The true moment root combines the two endpoint budgets and the
root interval length. The resulting power of the position scale is one. -/
namespace ArtinMatthews
noncomputable section

theorem giantTwoSidedRootInterval_length_le {X : ℝ} (hX : 1 ≤ X) :
    ((⌈2*X⌉₊-⌈X⌉₊ : ℕ) : ℝ) ≤ 2*X := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  rw [Nat.cast_sub (Nat.ceil_mono (by linarith : X ≤ 2*X))]
  have hlo := Nat.le_ceil X
  have hhi := (Nat.ceil_lt_add_one (mul_nonneg zero_le_two hX0)).le
  linarith

theorem giantTwoSidedPhysicalPairing_scalar (r : ℕ) {L X C E Ef Eg T cell : ℝ}
    (hL : 1 ≤ L) (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hf0 : 0 ≤ Ef) (hg0 : 0 ≤ Eg) (hT0 : 0 ≤ T) (hc0 : 0 ≤ cell)
    (hf : Ef ≤ X*L^(2*C)) (hg : Eg ≤ X*L^(2*C))
    (hT : T ≤ 2*X*(L^(-E))^(2*(r+1))) (hc : cell ≤ 2) :
    Real.sqrt 3 * Real.sqrt Eg * Ef^((r:ℝ)/(2*((r+1:ℕ):ℝ))) * cell *
      T^((2*((r+1:ℕ):ℝ))⁻¹) ≤ 8*X*L^(-E+2*C) := by
  let N := 2*(r+1)
  let a := (r:ℝ)/(N:ℝ)
  let b := ((N : ℝ)⁻¹)
  have hN : (N : ℝ) = 2*((r+1:ℕ):ℝ) := by simp only [N,Nat.cast_mul,Nat.cast_ofNat]
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by unfold N; omega)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have ha : 0 ≤ a := by unfold a; positivity
  have hb : 0 ≤ b := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hab : a+b = 1/2 := by
    unfold a b
    rw [hN,Nat.cast_add,Nat.cast_one]
    have hr : (r : ℝ)+1 ≠ 0 := by positivity
    field_simp
  have haC : (2*C)*a ≤ C := by
    have hale : a ≤ 1/2 := by linarith
    linarith only [mul_le_mul_of_nonneg_left hale (mul_nonneg zero_le_two hC)]
  have hf' : Ef^a ≤ X^a*L^C := by
    calc
      _ ≤ (X*L^(2*C))^a := Real.rpow_le_rpow hf0 hf ha
      _ = X^a*L^((2*C)*a) := by rw [Real.mul_rpow hX0.le (Real.rpow_nonneg hL0.le _), ← Real.rpow_mul hL0.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL haC) (Real.rpow_nonneg hX0.le _)
  have hg' : Real.sqrt Eg ≤ X^(1/2:ℝ)*L^C := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ ≤ (X*L^(2*C))^(1/2:ℝ) := Real.rpow_le_rpow hg0 hg (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow hX0.le (Real.rpow_nonneg hL0.le _), ← Real.rpow_mul hL0.le]
        congr 2
        ring
  have hT' : T^b ≤ 2*X^b*L^(-E) := by
    calc
      _ ≤ (2*X*(L^(-E))^N)^b := Real.rpow_le_rpow hT0 hT hb
      _ = (2:ℝ)^b*X^b*L^(-E) := by
        rw [Real.mul_rpow (mul_nonneg zero_le_two hX0.le) (pow_nonneg (Real.rpow_nonneg hL0.le _) _),
          Real.mul_rpow zero_le_two hX0.le, Real.pow_rpow_inv_natCast (Real.rpow_nonneg hL0.le _)
            (Nat.ne_of_gt (by positivity : 0 < N))]
      _ ≤ _ := by
        have hb1 : b ≤ 1 := inv_le_one_of_one_le₀ hN1
        have hb2 := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hb1).trans_eq (Real.rpow_one 2)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb2 (Real.rpow_nonneg hX0.le _))
          (Real.rpow_nonneg hL0.le _)
  have h3 : Real.sqrt 3 ≤ 2 := by
    calc
      _ ≤ Real.sqrt (2^2) := Real.sqrt_le_sqrt (by norm_num)
      _ = _ := Real.sqrt_sq zero_le_two
  rw [← hN]
  change Real.sqrt 3*Real.sqrt Eg*Ef^a*cell*T^b ≤ _
  calc
    _ ≤ Real.sqrt 3*(X^(1/2:ℝ)*L^C)*(X^a*L^C)*2*(2*X^b*L^(-E)) := by
      gcongr
    _ = (4*Real.sqrt 3)*(X^(1/2:ℝ)*(X^a*X^b))*((L^C*L^C)*L^(-E)) := by ring
    _ = (4*Real.sqrt 3)*X*L^(-E+2*C) := by
      rw [← Real.rpow_add hX0 a b, hab, ← Real.rpow_add hX0, ← Real.rpow_add hL0 C C,
        ← Real.rpow_add hL0, show (1/2:ℝ)+1/2=1 by norm_num, Real.rpow_one]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [h3]) hX0.le) (Real.rpow_nonneg hL0.le _)

end
end ArtinMatthews
