module

public import ArtinMatthews.GiantSamplingCofactors
public import ArtinMatthews.KloostermanWeakBound


set_option backward.privateInPublic true
@[expose] public section

/-! Summing the actual product gate over moduli costs one divisor count.
The ideal theta coefficient supplies the second divisor count. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

theorem giantCubicSampling_sum_moduli_norm_le (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ) (x : ℝ) (R u : ℕ)
    (z : ℂ) {C : ℝ} (hC : 0 ≤ C) (hz : ‖z‖ ≤ C) (hΦ : ‖Φ ((u : ℝ) / x)‖ ≤ 1) :
    (∑ r ∈ Finset.Icc 1 R, ‖z * giantCubicSamplingKernel η χ Φ x r u‖) ≤
      C * ((u + 1).divisors.card : ℝ) ^ 2 := by
  let Q := (Finset.Icc 1 R).filter (fun r => r ∣ u + 1)
  let D := (u + 1).divisors
  have hsub : Q ⊆ D := by
    intro r hr
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hr).2, Nat.succ_ne_zero u⟩
  have hsum : (∑ r ∈ Finset.Icc 1 R, ‖z * giantCubicSamplingKernel η χ Φ x r u‖) =
      ∑ r ∈ Q, ‖z * giantCubicSamplingKernel η χ Φ x r u‖ := by
    change _ = ∑ r ∈ (Finset.Icc 1 R).filter (fun r => r ∣ u + 1), _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases hd : r ∣ u + 1
    · simp only [hd, ite_true]
    · simp only [hd, ite_false, giantCubicSamplingKernel, mul_zero, norm_zero]
  rw [hsum]
  calc
    _ ≤ ∑ _r ∈ Q, C * (D.card : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hd := (Finset.mem_filter.mp hr).2
      have hker : ‖giantCubicSamplingKernel η χ Φ x r u‖ ≤ (D.card : ℝ) := by
        simp only [giantCubicSamplingKernel, hd, ite_true, norm_mul, Complex.norm_real]
        calc
          _ ≤ ‖Φ ((u : ℝ) / x)‖ * ‖idealThetaCoeff η (u + 1)‖ :=
            mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (χ.norm_le_one _)
          _ ≤ 1 * (D.card : ℝ) := mul_le_mul hΦ (idealThetaCoeff_norm_le_divisors_card η _)
            (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      rw [norm_mul]
      exact mul_le_mul hz hker (norm_nonneg _) hC
    _ = (Q.card : ℝ) * (C * (D.card : ℝ)) := by simp
    _ ≤ (D.card : ℝ) * (C * (D.card : ℝ)) :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsub))
        (mul_nonneg hC (Nat.cast_nonneg _))
    _ = _ := by ring

theorem giantCubicSampling_supported_sum_moduli_norm_le (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (ν : ℝ) (hν : 0 < ν) :
    ∃ Cν : ℝ, 0 < Cν ∧ ∀ (Φ : ℝ → ℝ) (x : ℝ) (R u : ℕ) (z : ℂ) (C : ℝ),
      1 ≤ x → 0 ≤ C → ‖z‖ ≤ C → (∀ t, ‖Φ t‖ ≤ 1) →
      Function.support Φ ⊆ Set.Ioo 1 2 →
      (∑ r ∈ Finset.Icc 1 R, ‖z * giantCubicSamplingKernel η χ Φ x r u‖) ≤
        C * Cν * x ^ (2 * ν) := by
  obtain ⟨C₀, hC₀, hpow⟩ := kloosterman_divisor_square_subpower
    (show (0 : ℝ) < 2 * ν by positivity)
  refine ⟨C₀ * (3 : ℝ) ^ (2 * ν), by positivity, ?_⟩
  intro Φ x R u z C hx hC hz hΦ hs
  by_cases hzero : Φ ((u : ℝ) / x) = 0
  · simp [giantCubicSamplingKernel, hzero]
    positivity
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hu : (u : ℝ) < 2 * x := (div_lt_iff₀ hx₀).mp (hs hzero).2
  have hux : ((u + 1 : ℕ) : ℝ) ≤ 3 * x := by push_cast; linarith
  have hsub : ((u + 1).divisors.card : ℝ) ^ 2 ≤
      C₀ * ((u + 1 : ℕ) : ℝ) ^ (2 * ν) := hpow _ (Nat.succ_le_succ (Nat.zero_le u))
  calc
    _ ≤ C * ((u + 1).divisors.card : ℝ) ^ 2 :=
      giantCubicSampling_sum_moduli_norm_le η χ Φ x R u z hC hz (hΦ _)
    _ ≤ C * (C₀ * ((u + 1 : ℕ) : ℝ) ^ (2 * ν)) := mul_le_mul_of_nonneg_left hsub hC
    _ ≤ C * (C₀ * (3 * x) ^ (2 * ν)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hux (by positivity)) hC₀.le) hC
    _ = _ := by rw [Real.mul_rpow (by norm_num) hx₀.le]; ring

end ArtinMatthews
