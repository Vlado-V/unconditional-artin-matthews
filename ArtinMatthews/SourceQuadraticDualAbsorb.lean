module

public import ArtinMatthews.SourceQuadraticDualLosses


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
noncomputable section

theorem quadraticDual_small_total_power_loss {M P K A η θ ε : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hA : 0 ≤ A) (hAK : A ≤ K) (hKM : K ≤ M)
    (hη : 0 ≤ η) (hsum : 3*η+θ ≤ ε) :
    ((A*P)^η * (2*P)^η) * (M*P)^θ ≤ (2:ℝ)^(2*η) * (M*P)^ε := by
  have hK : 0 ≤ K := hA.trans hAK
  have hMP : 1 ≤ M*P := one_le_mul_of_one_le_of_one_le hM hP
  have hOne : 1 ≤ (M*P)^η := Real.one_le_rpow hMP hη
  calc
    _ ≤ ((2*K*P)^η * (2*P)^η) * (M*P)^θ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      exact Real.rpow_le_rpow (by positivity) (by nlinarith) hη
    _ ≤ (((2*K*P)^η * (2*P)^η) * (M*P)^η) * (M*P)^θ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hOne) (by positivity)
    _ ≤ _ := quadraticDual_total_power_loss hM hP hK hKM hη hsum

theorem quadraticDual_weighted_total_power_loss {M P K η θ ε C L : ℝ}
    (hM : 1 ≤ M) (hP : 1 ≤ P) (hK : 0 ≤ K) (hKM : K ≤ M)
    (hη : 0 ≤ η) (hsum : 3*η+θ ≤ ε) (hC : 0 ≤ C) (hL : L ≤ C*(M*P)^η) :
    ((2*K*P)^η * (2*P)^η) * L * (M*P)^θ ≤ C * (2:ℝ)^(2*η) * (M*P)^ε := by
  calc
    _ ≤ ((2*K*P)^η * (2*P)^η) * (C*(M*P)^η) * (M*P)^θ := by gcongr
    _ = C * (((2*K*P)^η * (2*P)^η) * (M*P)^η * (M*P)^θ) := by ring
    _ ≤ C * ((2:ℝ)^(2*η) * (M*P)^ε) :=
      mul_le_mul_of_nonneg_left (quadraticDual_total_power_loss hM hP hK hKM hη hsum) hC
    _ = _ := by ring

end
end ArtinMatthews
