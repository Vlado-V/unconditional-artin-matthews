module

public import ArtinMatthews.CircleErrorRate
public import ArtinMatthews.CircleNormalizerSmoothBounds


set_option backward.privateInPublic true
@[expose] public section

/-! A quarter-power modulus envelope becomes a vanishing normalized circle
average. This disposes of a zero-frequency term after its Bessel estimate. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem circleAverage_norm_le (Q : Finset ℕ) (weight : ℕ → ℝ) (T : ℕ → ℂ)
    (B : ℝ) (hweight : ∀ q ∈ Q, 0 ≤ weight q) (hB : ∀ q ∈ Q, ‖T q‖ ≤ B)
    (hΛ : 0 < circleNormalizer Q weight) :
    ‖(∑ q ∈ Q, (weight q : ℂ) * T q) / (circleNormalizer Q weight : ℂ)‖ ≤
      B * (circleWeightMass Q weight / circleNormalizer Q weight) := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΛ]
  calc
    _ ≤ (∑ q ∈ Q, ‖(weight q : ℂ) * T q‖) / circleNormalizer Q weight :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hΛ.le
    _ ≤ (∑ q ∈ Q, weight q * B) / circleNormalizer Q weight := by
      apply div_le_div_of_nonneg_right _ hΛ.le
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hweight q hq)]
      exact mul_le_mul_of_nonneg_left (hB q hq) (hweight q hq)
    _ = _ := by rw [circleWeightMass, ← Finset.sum_mul]; ring

theorem circleAverage_quarter_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (F r L : ℕ), 0 < F → 0 < r → F.Coprime r →
      4 * (F * r) ≤ L → ∀ (T : ℕ → ℂ) (B : ℝ), 0 ≤ B →
      (∀ q ∈ circleModuli F r L, ‖T q‖ ≤ B * (q : ℝ)^(1/4 : ℝ)) →
      ‖(∑ q ∈ circleModuli F r L, (circleSmoothWeight L q : ℂ) * T q) /
          (circleNormalizer (circleModuli F r L) (circleSmoothWeight L) : ℂ)‖ ≤
        C * B * (F : ℝ) * (r : ℝ)^(1/4 : ℝ) / Real.sqrt L := by
  obtain ⟨C, hC, hrate⟩ := circleDetector_error_rate (1/4) (by norm_num) (by norm_num)
  refine ⟨C * (6 : ℝ)^(1/4 : ℝ), by positivity, ?_⟩
  intro F r L hF hr hFr hL T B hB hT
  have hLp : 0 < L := lt_of_lt_of_le (by positivity : 0 < 4 * (F * r)) hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLp
  have hweight : ∀ q ∈ circleModuli F r L, 0 ≤ circleSmoothWeight L q :=
    fun q _ => circleSmoothWeight_nonneg L q
  have hp : ∀ q : ℕ, 4 * L ≤ q → q ≤ 5 * L → 1 ≤ circleSmoothWeight L q :=
    fun q hq1 hq2 => (circleSmoothWeight_plateau hLp hq1 hq2).symm.le
  have hmass := hrate F r L hF hr hFr hL (circleSmoothWeight L) 1 (by norm_num)
    hweight (fun q _ => circleSmoothWeight_le_one L q) hp 1
  simp only [Nat.cast_one, one_pow, mul_one] at hmass
  have hsize : ∀ q ∈ circleModuli F r L, ‖T q‖ ≤ B * (6 * (L : ℝ))^(1/4 : ℝ) := by
    intro q hq
    have hqL : q ≤ 6 * L := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
    exact (hT q hq).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg q) (by exact_mod_cast hqL) (by norm_num)) hB)
  apply (circleAverage_norm_le (circleModuli F r L) (circleSmoothWeight L) T
    (B * (6 * (L : ℝ))^(1/4 : ℝ)) hweight hsize
    (circleSmoothNormalizer_positive hF hr hFr hL)).trans
  calc
    _ ≤ (B * (6 * (L : ℝ))^(1/4 : ℝ)) *
        (C * (F : ℝ) * (r : ℝ)^(1/4 : ℝ) * (L : ℝ)^((1/4 : ℝ)-1)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) hLR.le]
      have he : (L : ℝ)^(1/4 : ℝ) * (L : ℝ)^((1/4 : ℝ)-1) = (Real.sqrt L)⁻¹ := by
        rw [← Real.rpow_add hLR]
        norm_num
        rw [Real.rpow_neg hLR.le, ← Real.sqrt_eq_rpow]
      calc
        _ = (C * (6 : ℝ)^(1/4 : ℝ) * B * (F : ℝ) * (r : ℝ)^(1/4 : ℝ)) *
            ((L : ℝ)^(1/4 : ℝ) * (L : ℝ)^((1/4 : ℝ)-1)) := by ring
        _ = _ := by rw [he]; ring

end ArtinMatthews
