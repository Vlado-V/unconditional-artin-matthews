module

public import ArtinMatthews.MarkedMajorCharacterBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Absorption of the actual finite-major-cover measure cost. -/
namespace ArtinMatthews

 theorem markedMajor_cover_cost {L a P Y X Q : ℝ}
    (hL : 4 ≤ L) (hQ : 0 ≤ Q) (hQa : Q ≤ L^a) (hY : 0 ≤ Y) (hX : 0 ≤ X) :
    4*Q^3*((Y*X)*L^(-(P+3*a+1))) ≤ (Y*X)*L^(-P) := by
  have hLp : 0 < L := by linarith
  have hQ3 : Q^3 ≤ L^(3*a) := by
    calc
      _ ≤ (L^a)^3 := pow_le_pow_left₀ hQ hQa 3
      _ = L^(3*a) := by simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hLp.le a 3).symm
  have he : 4*L^(3*a)*L^(-(P+3*a+1)) = (4/L)*L^(-P) := by
    rw [mul_assoc,← Real.rpow_add hLp]
    have hp : 3*a+ -(P+3*a+1)= -P+(-1) := by ring
    rw [hp,Real.rpow_add hLp,Real.rpow_neg_one]
    ring
  calc
    _ ≤ 4*L^(3*a)*((Y*X)*L^(-(P+3*a+1))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ3 (by norm_num))
        (mul_nonneg (mul_nonneg hY hX) (Real.rpow_nonneg hLp.le _))
    _ = (Y*X)*((4/L)*L^(-P)) := by rw [← he]; ring
    _ ≤ (Y*X)*(1*L^(-P)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        ((div_le_one hLp).mpr hL) (Real.rpow_nonneg hLp.le _)) (mul_nonneg hY hX)
    _ = _ := by rw [one_mul]

end ArtinMatthews
