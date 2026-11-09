module

public import ArtinMatthews.SourceQuadraticDualWeightedRows


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

theorem quadraticDual_power_losses {M P K η : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hK : 0 ≤ K) (hKM : K ≤ M) (hη : 0 ≤ η) :
    (2*K*P)^η * (2*P)^η ≤ (2:ℝ)^(2*η) * (M*P)^(2*η) := by
  have hMP : 0 < M*P := mul_pos (zero_lt_one.trans_le hM) (zero_lt_one.trans_le hP)
  calc
    _ ≤ (2*(M*P))^η * (2*(M*P))^η := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by positivity) (by nlinarith) hη
      · exact Real.rpow_le_rpow (by positivity) (by nlinarith) hη
      · exact Real.rpow_nonneg (by positivity) _
      · exact Real.rpow_nonneg (by positivity) _
    _ = (2*(M*P))^(2*η) := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
    _ = _ := Real.mul_rpow (by norm_num) hMP.le

theorem quadraticDual_total_power_loss {M P K η θ ε : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hK : 0 ≤ K) (hKM : K ≤ M)
    (hη : 0 ≤ η) (hsum : 3*η+θ ≤ ε) :
    ((2*K*P)^η * (2*P)^η) * (M*P)^η * (M*P)^θ ≤
      (2:ℝ)^(2*η) * (M*P)^ε := by
  have hMP : 1 ≤ M*P := one_le_mul_of_one_le_of_one_le hM hP
  have hMP0 := zero_lt_one.trans_le hMP
  calc
    _ ≤ ((2:ℝ)^(2*η) * (M*P)^(2*η)) * (M*P)^η * (M*P)^θ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (quadraticDual_power_losses hM hP hK hKM hη)
          (Real.rpow_nonneg hMP0.le _)) (Real.rpow_nonneg hMP0.le _)
    _ = (2:ℝ)^(2*η) * (M*P)^(3*η+θ) := by
      rw [mul_assoc, ← Real.rpow_add hMP0, mul_assoc, ← Real.rpow_add hMP0]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hMP hsum) (Real.rpow_nonneg (by norm_num) _)

end
end ArtinMatthews

namespace ArtinMatthews.SourceEulerAssembly
open StandardAdelic VaryingKummerAnalytic
noncomputable section

theorem sourceQuadraticDual_dyad_length_bound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ M P K : ℝ, 1 ≤ M → 1 ≤ P → 1 ≤ K → K ≤ M →
      (sourceReflectionDyadLength K : ℝ) ≤ C*(M*P)^η := by
  obtain ⟨H, hH, hlog⟩ := sourceReflectionLogPower_le (K := 2) (m := 1)
    (by norm_num) zero_le_one hη 1 (by decide)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨H/Real.log 2, by positivity, ?_⟩
  intro M P K hM hP hK hKM
  have hk0 := zero_lt_one.trans_le hK
  have h := hlog K hK
  rw [pow_one, Real.rpow_one] at h
  calc
    _ ≤ Real.log (2*K)/Real.log 2 := sourceReflectionDyadLength_le_log hK
    _ ≤ H*K^η/Real.log 2 := div_le_div_of_nonneg_right h hlog2.le
    _ = (H/Real.log 2)*K^η := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hk0.le
      (hKM.trans (le_mul_of_one_le_right (zero_le_one.trans hM) hP)) hη.le) (by positivity)

end
end ArtinMatthews.SourceEulerAssembly
