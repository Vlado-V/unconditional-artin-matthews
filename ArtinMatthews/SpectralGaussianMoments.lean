module

public import ArtinMatthews.SpectralABLGaussianBound
public import Mathlib.Analysis.Normed.Algebra.Exponential


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory
noncomputable section

theorem spectralExp_monomial_bound (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.exp (-x) ≤ (n.factorial : ℝ) := by
  have hsum : HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have hterm := hsum.summable.le_tsum n (fun k _ => by positivity : ∀ k ≠ n, 0 ≤ x ^ k / (k.factorial : ℝ))
  rw [hsum.tsum_eq] at hterm
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hbound : x ^ n ≤ Real.exp x * (n.factorial : ℝ) := (div_le_iff₀ hfac).mp hterm
  calc
    _ ≤ (Real.exp x * (n.factorial : ℝ)) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hbound (Real.exp_nonneg _)
    _ = _ := by rw [mul_right_comm, ← Real.exp_add]; simp

theorem spectralGaussian_weight_moment (s : ℝ) (n : ℕ) :
    (1 + s ^ 2) ^ n * Real.exp (-(s ^ 2)) ≤ (2 : ℝ) ^ n * (n.factorial : ℝ) := by
  have hfac : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  by_cases hs : s ^ 2 ≤ 1
  · calc
      _ ≤ (2 : ℝ) ^ n * 1 := mul_le_mul
        (pow_le_pow_left₀ (by positivity) (by linarith : 1 + s ^ 2 ≤ 2) n)
        (Real.exp_le_one_iff.mpr (by nlinarith)) (Real.exp_nonneg _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hfac (by positivity)
  · have hs' : 1 ≤ s ^ 2 := (lt_of_not_ge hs).le
    calc
      _ ≤ (2 * s ^ 2) ^ n * Real.exp (-(s ^ 2)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) n) (Real.exp_nonneg _)
      _ = (2 : ℝ) ^ n * ((s ^ 2) ^ n * Real.exp (-(s ^ 2))) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (spectralExp_monomial_bound (s ^ 2) (sq_nonneg s) n) (by positivity)

theorem spectralGaussian_shifted_weight_bound (m Δ : ℝ) (hΔ : 0 < Δ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      (1 + t ^ 2) ^ n * Real.exp (-(((t - m) / Δ) ^ 2)) ≤ C := by
  let A := 1 + 2 * m ^ 2 + 2 * Δ ^ 2
  refine ⟨A ^ n * ((2 : ℝ) ^ n * (n.factorial : ℝ)), by dsimp [A]; positivity, ?_⟩
  intro t
  let s := (t - m) / Δ
  have ht : t = m + Δ * s := by dsimp [s]; field_simp; ring
  have hbase : 1 + t ^ 2 ≤ A * (1 + s ^ 2) := by
    rw [ht]
    dsimp [A]
    nlinarith [sq_nonneg (m - Δ * s), mul_nonneg (sq_nonneg m) (sq_nonneg s)]
  calc
    _ ≤ (A * (1 + s ^ 2)) ^ n * Real.exp (-(s ^ 2)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase n) (Real.exp_nonneg _)
    _ = A ^ n * ((1 + s ^ 2) ^ n * Real.exp (-(s ^ 2))) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (spectralGaussian_weight_moment s n) (by dsimp [A]; positivity)

end
end ArtinMatthews
