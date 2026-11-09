module

public import ArtinMatthews.PrimeExtractionWeightUniform
public import ArtinMatthews.PrimeExtractionSquarefulAsymptotic


set_option backward.privateInPublic true
@[expose] public section

/-! Removing bounded coefficients on the actual squareful rough set. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators Asymptotics

noncomputable def markedSquarefulCoefficientSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (b G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ x : ℝ) : ℂ :=
  ∑ n ∈ roughNonsquarefreeUpTo ⌊T * x⌋₊ (x ^ γ), markedExtractionWeight e G Φ x n * b x n

theorem markedSquarefulCoefficientSum_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (b G : ℝ → ℕ → ℂ)
    {CG : ℝ} (hCG : 0 ≤ CG) (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T γ B : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ)
    (hb : ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ T * x →
      MarkedRoughAbove (x ^ γ) n → ‖b x n‖ ≤ B) (A : ℝ) :
    markedSquarefulCoefficientSum e b G Φ T γ =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  classical
  obtain ⟨C, hC, hw⟩ := markedExtractionWeight_bound e he G hCG hG Φ hΦ hT
  have hbigO : markedSquarefulCoefficientSum e b G Φ T γ =O[atTop] roughNonsquarefreeCount T γ := by
    apply Asymptotics.IsBigO.of_bound (C * B)
    filter_upwards [hw, hb, eventually_gt_atTop (0 : ℝ)] with x hwx hbx hx
    have hterm : ∀ n ∈ roughNonsquarefreeUpTo ⌊T * x⌋₊ (x ^ γ),
        ‖markedExtractionWeight e G Φ x n * b x n‖ ≤ C * B := by
      intro n hn
      obtain ⟨hnrange, hn0, hnrough, _⟩ := Finset.mem_filter.mp hn
      have hnT : (n : ℝ) ≤ T * x :=
        (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hnrange))).trans
          (Nat.floor_le (mul_nonneg hT hx.le))
      rw [norm_mul]
      exact mul_le_mul (hwx n hnT) (hbx n hn0 hnT hnrough) (norm_nonneg _) hC
    calc
      _ ≤ ∑ n ∈ roughNonsquarefreeUpTo ⌊T * x⌋₊ (x ^ γ),
          ‖markedExtractionWeight e G Φ x n * b x n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ roughNonsquarefreeUpTo ⌊T * x⌋₊ (x ^ γ), C * B := Finset.sum_le_sum hterm
      _ = (C * B) * ‖roughNonsquarefreeCount T γ x‖ := by
        rw [Real.norm_of_nonneg (show 0 ≤ roughNonsquarefreeCount T γ x from Nat.cast_nonneg _)]
        simp only [roughNonsquarefreeCount, Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact hbigO.trans_isLittleO (roughNonsquarefreeCount_isLittleO hT hγ A)

end ArtinMatthews
