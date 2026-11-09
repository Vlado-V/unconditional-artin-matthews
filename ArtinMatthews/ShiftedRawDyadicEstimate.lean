module

public import ArtinMatthews.ShiftedRawDyadicTarget
public import ArtinMatthews.ShiftedDyadicSmoothEnergy
public import ArtinMatthews.ShiftedDyadicWeightedCS
public import ArtinMatthews.CubicThetaActualReal


set_option backward.privateInPublic true
@[expose] public section

/-! The raw dyadic estimate from the actual correlation source. -/
namespace ArtinMatthews
open OAI.SevenEighths
open scoped BigOperators
noncomputable section

theorem shiftedRawDyadicBound_of_correlation (N : ℕ) (η : HeckeFamily.Character)
    (hreal : ∀ n, star (idealThetaCoeff η n) = idealThetaCoeff η n)
    (hsource : ShiftedABLCorrelationSource N η) :
    ∀ ν : ℝ, 0 < ν → ∃ C : ℝ, 0 < C ∧ ShiftedRawDyadicBound N η ν C := by
  intro ν hν
  let ε := min ν (1 / 4)
  have hε : 0 < ε := lt_min hν (by norm_num)
  have hεν : ε ≤ ν := min_le_left _ _
  have hεsmall : ε < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨C0, hC0, henergy⟩ := shiftedDyadic_scaledBump_energy_bound N η hreal hsource ε hε hεsmall
  obtain ⟨CL, hCL, hlow⟩ := shiftedDyadic_theta_subpower ν hν
  let CH := Real.sqrt (8 * C0)
  have hCH : 0 < CH := Real.sqrt_pos.mpr (by positivity)
  refine ⟨CL + CH, add_pos hCL hCH, ?_⟩
  intro M T hM hT A B hA hB hSF hN α β hα hβ
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M from hM)
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T from hT)
  let R := (M : ℝ) * T
  let W := Real.sqrt M * T + (M : ℝ) ^ (5 / 4 : ℝ) * (T : ℝ) ^ (7 / 8 : ℝ)
  have hR1 : 1 ≤ R := by dsimp [R]; nlinarith
  have hR0 : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR1
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  change ‖shiftedRawThetaBilinear η A B α β‖ ≤ (CL + CH) * R ^ ν * W
  by_cases hregion : T ≤ M ^ 2
  · have hraw : ‖shiftedRawThetaBilinear η A B α β‖ ≤ CL * R ^ ν * R := by
      simpa only [shiftedRawThetaBilinear, R] using hlow η M T hM hT A B hA hB α β hα hβ
    have hRle : R ≤ W := by
      have h := shiftedBilinear_lowRegion_power M T hM1 hT1 (by exact_mod_cast hregion)
      exact h.trans (le_add_of_nonneg_left (by positivity))
    calc
      _ ≤ CL * R ^ ν * R := hraw
      _ ≤ CL * R ^ ν * W :=
        mul_le_mul_of_nonneg_left hRle (mul_nonneg hCL.le (Real.rpow_nonneg hR0 _))
      _ ≤ (CL + CH) * R ^ ν * W :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCH.le) (Real.rpow_nonneg hR0 _)) hW0
  · have hT2 : 2 ≤ T := by
      have hM2 : 0 < M ^ 2 := pow_pos hM _
      omega
    have hT2real : (2 : ℝ) ≤ T := by exact_mod_cast hT2
    have hregionReal : (M : ℝ) ^ 2 ≤ T := by
      exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hregion))
    let S1 := shiftedBilinearMajorantScale1 T
    let S2 := shiftedBilinearMajorantScale2 T
    have hsc := shiftedBilinearMajorant_scales T hT2real
    have hS1 : S1 ≤ 2 * (T : ℝ) := hsc.2.2.1.trans (by linarith)
    let E1 := ∑ n ∈ Finset.Icc 1 ⌈2 * S1⌉₊, (shiftedBilinearScaledBump S1 n).re *
      ‖∑ m ∈ A, α m * idealThetaCoeff η (m * n + 1)‖ ^ 2
    let E2 := ∑ n ∈ Finset.Icc 1 ⌈2 * S2⌉₊, (shiftedBilinearScaledBump S2 n).re *
      ‖∑ m ∈ A, α m * idealThetaCoeff η (m * n + 1)‖ ^ 2
    let P := (M : ℝ) * T + (M : ℝ) ^ 3 * (T : ℝ) ^ (1 / 2 : ℝ) +
      (M : ℝ) ^ (5 / 2 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)
    let E := 4 * C0 * R ^ (2 * ε) * P
    have hE1 : E1 ≤ C0 * R ^ (2 * ε) * P :=
      henergy M hM T S1 hT1 hsc.1 hS1 A hA hSF hN α hα
    have hE2 : E2 ≤ C0 * R ^ (2 * ε) * P :=
      henergy M hM T S2 hT1 hsc.2.1 hsc.2.2.2.2 A hA hSF hN α hα
    have hCS : ‖shiftedRawThetaBilinear η A B α β‖ ^ 2 ≤ 2 * (T : ℝ) * (E1 + E2) := by
      simpa only [shiftedRawThetaBilinear, E1, E2, S1, S2] using
        shiftedDyadic_twoBump_cauchy T hT2 A B hB α β
          (fun m n => idealThetaCoeff η (m * n + 1)) hβ
    have hCS' : ‖shiftedRawThetaBilinear η A B α β‖ ^ 2 ≤ (T : ℝ) * E := by
      calc
        _ ≤ 2 * (T : ℝ) * (E1 + E2) := hCS
        _ ≤ 2 * (T : ℝ) * (C0 * R ^ (2 * ε) * P + C0 * R ^ (2 * ε) * P) :=
          mul_le_mul_of_nonneg_left (add_le_add hE1 hE2) (by positivity)
        _ = (T : ℝ) * E := by dsimp [E]; ring
    have hE0 : 0 ≤ E := by dsimp [E, P, R]; positivity
    have hconst : 2 * (4 * C0) = 8 * C0 := by ring
    have heps : (2 * ε) / 2 = ε := by ring
    have hExtract : ‖shiftedRawThetaBilinear η A B α β‖ ≤ CH * R ^ ε * W := by
      simpa only [CH, R, W, hconst, heps] using
        shiftedBilinear_squaredBudget (M : ℝ) (T : ℝ) ‖shiftedRawThetaBilinear η A B α β‖
          (4 * C0) E (2 * ε) hM1 hT1 (norm_nonneg _) (by positivity) hE0 hCS'
          (show E ≤ 4 * C0 * ((M : ℝ) * T) ^ (2 * ε) *
            ((M : ℝ) * T + (M : ℝ) ^ 3 * (T : ℝ) ^ (1 / 2 : ℝ) +
              (M : ℝ) ^ (5 / 2 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ)) from le_rfl) hregionReal
    calc
      _ ≤ CH * R ^ ε * W := hExtract
      _ ≤ CH * R ^ ν * W := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR1 hεν) hCH.le) hW0
      _ ≤ (CL + CH) * R ^ ν * W :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCL.le) (Real.rpow_nonneg hR0 _)) hW0

theorem cubicNumerator_shiftedRawDyadicBound (N : ℕ) (a : ℤ) (ha : a ≠ 0)
    (hsource : ShiftedABLCorrelationSource N (cubicNumeratorHeckeCharacter a ha)) :
    ∀ ν : ℝ, 0 < ν → ∃ C : ℝ, 0 < C ∧
      ShiftedRawDyadicBound N (cubicNumeratorHeckeCharacter a ha) ν C :=
  shiftedRawDyadicBound_of_correlation N (cubicNumeratorHeckeCharacter a ha)
    (cubicNumeratorThetaCoeff_conjugate a ha) hsource

end
end ArtinMatthews
