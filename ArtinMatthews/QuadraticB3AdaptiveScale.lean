module

public import ArtinMatthews.QuadraticB3TailScale


set_option backward.privateInPublic true
@[expose] public section

/-! Scalar estimates for the two adaptive dual-contour lines. -/
namespace ArtinMatthews.QuadraticScale
noncomputable section

private theorem adaptive_first_factor {M P A : ℝ}
    (hM : 0 < M) (hP : 0 < P) (hA : 0 < A) (σ : ℝ) :
    M ^ (1 - σ / 2) * P ^ σ * A ^ (-σ / 2) =
      M * (P ^ 2 / (M * A)) ^ (σ / 2) := by
  have hneg : -σ / 2 = -(σ / 2) := by ring
  rw [Real.rpow_sub hM, Real.rpow_one, hneg, Real.rpow_neg hA.le,
    Real.div_rpow (sq_nonneg P) (mul_nonneg hM.le hA.le),
    Real.mul_rpow hM.le hA.le, ← Real.rpow_two P, ← Real.rpow_mul hP.le,
    show 2 * (σ / 2) = σ by ring]
  ring

private theorem adaptive_second_factor {M P A : ℝ}
    (hM : 0 < M) (hP : 0 < P) (hA : 0 < A) (σ α : ℝ) :
    M ^ (1 - σ / 2) * P ^ (σ - 1) * A ^ (α - σ / 2) =
      Real.sqrt M * A ^ (α - 1 / 2) * (M * A / P ^ 2) ^ ((1 - σ) / 2) := by
  symm
  rw [Real.sqrt_eq_rpow, Real.div_rpow (mul_nonneg hM.le hA.le) (sq_nonneg P),
    Real.mul_rpow hM.le hA.le, ← Real.rpow_two P, ← Real.rpow_mul hP.le]
  calc
    _ = (M ^ (1 / 2 : ℝ) * M ^ ((1 - σ) / 2)) *
        (A ^ (α - 1 / 2) * A ^ ((1 - σ) / 2)) / P ^ (2 * ((1 - σ) / 2)) := by ring
    _ = M ^ ((1 / 2 : ℝ) + (1 - σ) / 2) *
        A ^ ((α - 1 / 2) + (1 - σ) / 2) / P ^ (2 * ((1 - σ) / 2)) := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hA]
    _ = M ^ (1 - σ / 2) * A ^ (α - σ / 2) / P ^ (1 - σ) := by
      rw [show (1 / 2 : ℝ) + (1 - σ) / 2 = 1 - σ / 2 by ring,
        show (α - 1 / 2) + (1 - σ) / 2 = α - σ / 2 by ring,
        show 2 * ((1 - σ) / 2) = 1 - σ by ring]
    _ = _ := by
      rw [show σ - 1 = -(1 - σ) by ring, Real.rpow_neg hP.le]
      ring

private theorem adaptive_prime_factor {P : ℝ} (hP : 0 < P) (σ : ℝ) :
    P ^ (σ - 1) * P = P ^ σ := by
  rw [Real.rpow_sub hP, Real.rpow_one]
  exact div_mul_cancel₀ _ hP.ne'

theorem quadraticB3_small_whole_ball_scale {M P K A α θ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hK : 1 ≤ K) (hKM : K ≤ M)
    (hA : 0 < A) (hAK : A ≤ K) (hAT : A ≤ P ^ 2 / M)
    (hα : 1 ≤ α) (hθ : 0 < θ) (hθone : θ < 1) :
    M ^ (1 - θ / 2) * P ^ (θ - 1) * (P + A ^ α) ≤
      (M * P) ^ θ * (M + Real.sqrt M * K ^ (α - 1 / 2)) := by
  have hM0 := zero_lt_one.trans_le hM
  have hP0 := zero_lt_one.trans_le hP
  have hK0 := zero_lt_one.trans_le hK
  have hT : 1 ≤ M * P := one_le_mul_of_one_le_of_one_le hM hP
  have hT0 := zero_lt_one.trans_le hT
  have hfirst : M ^ (1 - θ / 2) * P ^ (θ - 1) * P ≤ (M * P) ^ θ * M := by
    rw [mul_assoc, adaptive_prime_factor hP0]
    have hMpow : M ^ (1 - θ / 2) ≤ M := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM
        (show 1 - θ / 2 ≤ 1 by linarith)
    have hPpow : P ^ θ ≤ (M * P) ^ θ := Real.rpow_le_rpow hP0.le
      (le_mul_of_one_le_left hP0.le hM) hθ.le
    have hm := mul_le_mul hMpow hPpow (Real.rpow_nonneg hP0.le _) hM0.le
    simpa only [mul_comm] using hm
  have hratio : M * A / P ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hP0)).mpr
    simpa only [mul_comm] using (le_div_iff₀ hM0).mp hAT
  have hratioPow : (M * A / P ^ 2) ^ ((1 - θ) / 2) ≤ 1 :=
    Real.rpow_le_one (by positivity) hratio (by linarith)
  have hApow : A ^ (α - 1 / 2) ≤ K ^ (α - 1 / 2) :=
    Real.rpow_le_rpow hA.le hAK (by linarith)
  have hAtheta : A ^ (θ / 2) ≤ (M * P) ^ θ := by
    refine (Real.rpow_le_rpow hA.le
      (hAK.trans (hKM.trans (le_mul_of_one_le_right hM0.le hP))) (by positivity)).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hsecond : M ^ (1 - θ / 2) * P ^ (θ - 1) * A ^ α ≤
      (M * P) ^ θ * (Real.sqrt M * K ^ (α - 1 / 2)) := by
    have hsplit : A ^ α = A ^ (α - θ / 2) * A ^ (θ / 2) := by
      rw [← Real.rpow_add hA, show α - θ / 2 + θ / 2 = α by ring]
    calc
      _ = (M ^ (1 - θ / 2) * P ^ (θ - 1) * A ^ (α - θ / 2)) * A ^ (θ / 2) := by
        rw [hsplit]
        ring
      _ = (Real.sqrt M * A ^ (α - 1 / 2) * (M * A / P ^ 2) ^ ((1 - θ) / 2)) *
          A ^ (θ / 2) := by rw [adaptive_second_factor hM0 hP0 hA]
      _ ≤ (Real.sqrt M * K ^ (α - 1 / 2) * 1) * (M * P) ^ θ := by
        gcongr
      _ = _ := by ring
  calc
    _ = M ^ (1 - θ / 2) * P ^ (θ - 1) * P +
        M ^ (1 - θ / 2) * P ^ (θ - 1) * A ^ α := by ring
    _ ≤ (M * P) ^ θ * M + (M * P) ^ θ * (Real.sqrt M * K ^ (α - 1 / 2)) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

theorem quadraticB3_large_weighted_rows_scale {M P K L α θ : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hK : 1 ≤ K) (hKM : K ≤ M)
    (hL : 1 ≤ L) (hLT : P ^ 2 / M ≤ L)
    (_hα : 1 ≤ α) (hθ : 0 < θ) (hθone : θ < 1) :
    M ^ (1 - (1 - θ) / 2) * P ^ ((1 - θ) - 1) *
        (P * L ^ (-(1 - θ) / 2) + K ^ (α - (1 - θ) / 2)) ≤
      (M * P) ^ θ * (M + Real.sqrt M * K ^ (α - 1 / 2)) := by
  have hM0 := zero_lt_one.trans_le hM
  have hP0 := zero_lt_one.trans_le hP
  have hK0 := zero_lt_one.trans_le hK
  have hL0 := zero_lt_one.trans_le hL
  have hT : 1 ≤ M * P := one_le_mul_of_one_le_of_one_le hM hP
  have hT0 := zero_lt_one.trans_le hT
  have hfirst : M ^ (1 - (1 - θ) / 2) * P ^ ((1 - θ) - 1) *
      (P * L ^ (-(1 - θ) / 2)) ≤ (M * P) ^ θ * M := by
    have hratio : P ^ 2 / (M * L) ≤ 1 := by
      apply (div_le_one (mul_pos hM0 hL0)).mpr
      simpa only [mul_comm] using (div_le_iff₀ hM0).mp hLT
    calc
      _ = M ^ (1 - (1 - θ) / 2) * P ^ (1 - θ) * L ^ (-(1 - θ) / 2) := by
        calc
          _ = M ^ (1 - (1 - θ) / 2) * (P ^ ((1 - θ) - 1) * P) *
              L ^ (-(1 - θ) / 2) := by ring
          _ = _ := by rw [adaptive_prime_factor hP0]
      _ = M * (P ^ 2 / (M * L)) ^ ((1 - θ) / 2) := adaptive_first_factor hM0 hP0 hL0 _
      _ ≤ M := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.rpow_le_one (by positivity) hratio (by linarith)) hM0.le
      _ ≤ _ := le_mul_of_one_le_left hM0.le (Real.one_le_rpow hT hθ.le)
  have hratio : M * K / P ^ 2 ≤ (M * P) ^ 2 := by
    have hP2 : 1 ≤ P ^ 2 := one_le_pow₀ hP
    calc
      _ ≤ M * K := div_le_self (by positivity) hP2
      _ ≤ M * M := mul_le_mul_of_nonneg_left hKM hM0.le
      _ ≤ (M * P) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self hM0.le
          (le_mul_of_one_le_right hM0.le hP)
  have hratioPow : (M * K / P ^ 2) ^ (θ / 2) ≤ (M * P) ^ θ := by
    calc
      _ ≤ ((M * P) ^ 2) ^ (θ / 2) := Real.rpow_le_rpow (by positivity) hratio (by positivity)
      _ = _ := by
        rw [← Real.rpow_two, ← Real.rpow_mul hT0.le, show 2 * (θ / 2) = θ by ring]
  have hsecond : M ^ (1 - (1 - θ) / 2) * P ^ ((1 - θ) - 1) *
      K ^ (α - (1 - θ) / 2) ≤ (M * P) ^ θ * (Real.sqrt M * K ^ (α - 1 / 2)) := by
    rw [adaptive_second_factor hM0 hP0 hK0,
      show (1 - (1 - θ)) / 2 = θ / 2 by ring]
    have hm := mul_le_mul_of_nonneg_left hratioPow
      (mul_nonneg (Real.sqrt_nonneg M) (Real.rpow_nonneg hK0.le (α - 1 / 2)))
    simpa only [mul_comm] using hm
  calc
    _ = M ^ (1 - (1 - θ) / 2) * P ^ ((1 - θ) - 1) * (P * L ^ (-(1 - θ) / 2)) +
        M ^ (1 - (1 - θ) / 2) * P ^ ((1 - θ) - 1) * K ^ (α - (1 - θ) / 2) := by ring
    _ ≤ (M * P) ^ θ * M + (M * P) ^ θ * (Real.sqrt M * K ^ (α - 1 / 2)) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

end
end ArtinMatthews.QuadraticScale
