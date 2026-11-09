module

public import ArtinMatthews.ShiftedABLSourceBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The retained dual coefficient factor is reduced to the original
source scale, keeping all small exponents explicit. -/

noncomputable section
namespace ArtinMatthews

theorem shiftedABL_retained_coefficient_bound
    {P Q H K1 K2 A ε v : ℝ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hH : 1 ≤ H) (hA : 0 ≤ A)
    (hε : 0 ≤ ε) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hQup : Q ≤ P^A)
    (hcut1 : K1 ≤ 8*P^ε*Q^2/H) (hcut2 : K2 ≤ 8*P^ε*Q^2/H) :
    (K1*K2)^((1+v)/2) ≤ 64*P^(2*ε+2*A*v)*Q^2/H := by
  let U := 8*P^ε*Q^2/H
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hU0 : 0 < U := by dsimp [U]; positivity
  have hPtwo : (P^A)^2=P^(2*A) := by
    rw [← Real.rpow_natCast (P^A) 2,← Real.rpow_mul hP0.le]
    congr 1
    norm_num
    ring
  have hUup : U ≤ 8*P^(ε+2*A) := by
    calc
      U ≤ 8*P^ε*Q^2 := div_le_self (by positivity) hH
      _ ≤ 8*P^ε*(P^A)^2 := by gcongr
      _ = _ := by rw [hPtwo,Real.rpow_add hP0]; ring
  have hsmall : U^v ≤ 8*P^(ε+2*A*v) := by
    calc
      _ ≤ (8*P^(ε+2*A))^v := Real.rpow_le_rpow hU0.le hUup hv
      _ = (8 : ℝ)^v * P^((ε+2*A)*v) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hP0.le _),← Real.rpow_mul hP0.le]
      _ ≤ 8*P^(ε+2*A*v) := mul_le_mul
        (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hv1)
        (Real.rpow_le_rpow_of_exponent_le hP
          (by nlinarith [mul_le_mul_of_nonneg_left hv1 hε]))
        (Real.rpow_nonneg hP0.le _) (by norm_num)
  have hprod : K1*K2 ≤ U^2 := by
    calc
      K1*K2 ≤ U*U := mul_le_mul hcut1 hcut2 hK2 hU0.le
      _ = U^2 := by ring
  calc
    _ ≤ (U^2)^((1+v)/2) := Real.rpow_le_rpow (mul_nonneg hK1 hK2) hprod (by positivity)
    _ = U*U^v := by
      rw [← Real.rpow_natCast U 2,← Real.rpow_mul hU0.le]
      change U^((2 : ℝ)*((1+v)/2))=U*U^v
      rw [show (2 : ℝ)*((1+v)/2)=1+v by ring,Real.rpow_add hU0,Real.rpow_one]
    _ ≤ U*(8*P^(ε+2*A*v)) := mul_le_mul_of_nonneg_left hsmall hU0.le
    _ = 64*P^(2*ε+2*A*v)*Q^2/H := by
      have he : P^ε*P^(ε+2*A*v)=P^(2*ε+2*A*v) := by
        calc
          _ = P^(ε+(ε+2*A*v)) := (Real.rpow_add hP0 _ _).symm
          _ = _ := by congr 1; ring
      calc
        _ = 64*(P^ε*P^(ε+2*A*v))*Q^2/H := by dsimp [U]; ring
        _ = _ := by rw [he]

end ArtinMatthews
