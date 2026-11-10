module

public import ArtinMatthews.ShiftedLegendreIntervalLp
public import ArtinMatthews.ShiftedLegendreMoments
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.Positivity.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Orthogonality and exact norms from the monomial moments. -/
namespace ArtinMatthews
open MeasureTheory Polynomial
open scoped BigOperators Polynomial
noncomputable section

theorem shiftedLegendreValue_sum (n : ℕ) (x : ℝ) :
    shiftedLegendreValue n x =
      ∑ k ∈ Finset.range (n + 1), ((shiftedLegendre n).coeff k : ℝ) * x ^ k := by
  have h := congrArg (fun p : ℤ[X] => aeval x p) (shiftedLegendre n).as_sum_range_C_mul_X_pow
  simpa only [shiftedLegendreValue, Polynomial.natDegree_shiftedLegendre, map_sum, map_mul,
    map_pow, Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_int_eq, Int.coe_castRingHom] using h

theorem shiftedLegendreValue_moment_zero {n m : ℕ} (h : m < n) :
    (∫ x in (0 : ℝ)..1, x ^ m * shiftedLegendreValue n x) = 0 := by
  simp [shiftedLegendreValue, integral_pow_shiftedLegendre, Nat.descFactorial_of_lt h]

theorem shiftedLegendreValue_pair_sum (m n : ℕ) :
    (∫ x in (0 : ℝ)..1, shiftedLegendreValue m x * shiftedLegendreValue n x) =
      ∑ k ∈ Finset.range (m + 1), ((shiftedLegendre m).coeff k : ℝ) *
        (∫ x in (0 : ℝ)..1, x ^ k * shiftedLegendreValue n x) := by
  calc
    _ = ∫ x in (0 : ℝ)..1, ∑ k ∈ Finset.range (m + 1),
        ((shiftedLegendre m).coeff k : ℝ) * (x ^ k * shiftedLegendreValue n x) := by
      apply intervalIntegral.integral_congr
      intro x _
      change shiftedLegendreValue m x * shiftedLegendreValue n x = _
      rw [shiftedLegendreValue_sum m, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_assoc]
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul]
      · intro k _
        exact (continuous_const.mul ((continuous_id.pow k).mul
          (shiftedLegendreValue_continuous n))).intervalIntegrable _ _

theorem integral_shiftedLegendreValue_mul_of_lt {m n : ℕ} (hmn : m < n) :
    (∫ x in (0 : ℝ)..1, shiftedLegendreValue m x * shiftedLegendreValue n x) = 0 := by
  rw [shiftedLegendreValue_pair_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [shiftedLegendreValue_moment_zero ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans_lt hmn),
    mul_zero]

theorem integral_shiftedLegendreValue_sq (n : ℕ) :
    (∫ x in (0 : ℝ)..1, shiftedLegendreValue n x * shiftedLegendreValue n x) =
      (2 * (n : ℝ) + 1)⁻¹ := by
  rw [shiftedLegendreValue_pair_sum, Finset.sum_eq_single n]
  · change ((shiftedLegendre n).coeff n : ℝ) *
        (∫ x in (0 : ℝ)..1, x ^ n * aeval x (shiftedLegendre n)) = _
    rw [integral_pow_shiftedLegendre, Nat.descFactorial_self, Polynomial.coeff_shiftedLegendre,
      Nat.choose_self]
    push_cast
    simp only [mul_one]
    have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← pow_two, ← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    have hchoose : ((n + n).choose n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) =
        ((n + n).factorial : ℝ) := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n n
    calc
      _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
          (((n + n).choose n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ)) /
          ((n + n + 1).factorial : ℝ) := by ring
      _ = ((n + n).factorial : ℝ) / ((n + n + 1).factorial : ℝ) := by
        rw [hsign, hchoose, one_mul]
      _ = _ := by
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        rw [show (n : ℝ) + n + 1 = 2 * (n : ℝ) + 1 by ring]
        have hfact : ((n + n).factorial : ℝ) ≠ 0 := by positivity
        have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hfact, hn]
  · intro k hk hkn
    have hlt : k < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkn
    rw [shiftedLegendreValue_moment_zero hlt, mul_zero]
  · intro hn
    exact (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

theorem integral_shiftedLegendreValue_mul (m n : ℕ) :
    (∫ x in (0 : ℝ)..1, shiftedLegendreValue m x * shiftedLegendreValue n x) =
      if m = n then (2 * (n : ℝ) + 1)⁻¹ else 0 := by
  by_cases h : m = n
  · subst m
    simp [integral_shiftedLegendreValue_sq]
  · rw [ite_eq_right h]
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact integral_shiftedLegendreValue_mul_of_lt hlt
    · simpa only [mul_comm (shiftedLegendreValue n _) (shiftedLegendreValue m _)] using
        integral_shiftedLegendreValue_mul_of_lt hgt

theorem shiftedLegendreVector_inner (m n : ℕ) :
    inner ℂ (shiftedLegendreVector m) (shiftedLegendreVector n) =
      if m = n then (((2 * (n : ℝ) + 1)⁻¹ : ℝ) : ℂ) else 0 := by
  rw [shiftedLegendreVector_inner_interval, integral_shiftedLegendreValue_mul]
  split <;> simp_all

theorem shiftedLegendreVector_norm_sq (n : ℕ) :
    ‖shiftedLegendreVector n‖ ^ 2 = (2 * (n : ℝ) + 1)⁻¹ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), shiftedLegendreVector_inner, ite_eq_left rfl]
  exact RCLike.ofReal_re _

end
end ArtinMatthews
