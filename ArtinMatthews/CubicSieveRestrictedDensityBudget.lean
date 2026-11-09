module

public import ArtinMatthews.CubicSieveRestrictedDensity
public import ArtinMatthews.DivisorBound


set_option backward.privateInPublic true
@[expose] public section

/-! The actual primes removed by r and the reciprocal-square perturbation
of the independent marking probabilities have explicit finite budgets. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_markingSquareMass_le (P : Finset ℕ) {y M : ℝ} (hy : 0 < y)
    (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) (hmass : (∑ p ∈ P, 1 / (p : ℝ)) ≤ M) :
    (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ M / y := by
  calc
    _ ≤ ∑ p ∈ P, (1 / y) * (1 / (p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hp₀ : 0 < (p : ℝ) := hy.trans_le (hmin p hp)
      have h := mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hy (hmin p hp))
        (one_div_nonneg.mpr hp₀.le)
      simpa only [pow_two, one_div_mul_one_div] using h
    _ = (1 / y) * ∑ p ∈ P, 1 / (p : ℝ) := (mul_sum _ _ _).symm
    _ ≤ M / y := (mul_le_mul_of_nonneg_left hmass (one_div_nonneg.mpr hy.le)).trans_eq (by ring)

theorem cubicSieve_excludedMarkingMass_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {r : ℕ} (hr : 0 < r) {y : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) :
    (∑ p ∈ P.filter (fun p => p ∣ r), 1 / (p : ℝ)) ≤
      Real.log (r : ℝ) / (Real.log (3 / 2 : ℝ) * y) := by
  let R := P.filter (fun p => p ∣ r)
  have hc : (R.card : ℝ) ≤ Real.log (r : ℝ) / Real.log (3 / 2 : ℝ) :=
    card_le_log_div_log_of_primes_dvd hr (by norm_num)
      (fun p hp => hP p (mem_filter.mp hp).1)
      (fun p hp => by
        have htwo : (2 : ℝ) ≤ p := by exact_mod_cast (hP p (mem_filter.mp hp).1).two_le
        linarith only [htwo])
      (fun _ hp => (mem_filter.mp hp).2)
  calc
    _ ≤ ∑ _p ∈ R, (1 / y) := sum_le_sum (fun p hp =>
      one_div_le_one_div_of_le hy (hmin p (mem_filter.mp hp).1))
    _ = (R.card : ℝ) / y := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := (div_le_div_of_nonneg_right hc hy.le).trans_eq (by ring)

theorem cubicSieve_restrictedDensity_total_distance (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {r : ℕ} (hr : 0 < r) {y M : ℝ} (hy : 0 < y)
    (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) (hmass : (∑ p ∈ P, 1 / (p : ℝ)) ≤ M) :
    (∑ p ∈ P, |cubicSieveRestrictedMarkingDensity r p 1 - 1 / (p : ℝ)|) ≤
      M / y + Real.log (r : ℝ) / (Real.log (3 / 2 : ℝ) * y) := by
  calc
    _ ≤ ∑ p ∈ P, (1 / (p : ℝ) ^ 2 + if p ∣ r then 1 / (p : ℝ) else 0) := by
      apply sum_le_sum
      intro p hp
      rw [cubicSieve_restrictedMarkingDensity_distance r (hP p hp)]
      split_ifs <;> linarith [show (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 by positivity]
    _ = (∑ p ∈ P, 1 / (p : ℝ) ^ 2) +
      ∑ p ∈ P.filter (fun p => p ∣ r), 1 / (p : ℝ) := by rw [sum_add_distrib, sum_filter]
    _ ≤ _ := add_le_add (cubicSieve_markingSquareMass_le P hy hmin hmass)
      (cubicSieve_excludedMarkingMass_le P hP hr hy hmin)

theorem cubicSieve_restrictedDensity_total_tangent (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ) {y Z M : ℝ} (hy : 0 < y) (hZ : 1 ≤ Z)
    (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) (hmax : ∀ p ∈ P, (p : ℝ) ≤ Z)
    (hmass : (∑ p ∈ P, 1 / (p : ℝ)) ≤ M) :
    (∑ p ∈ P, |cubicSieveRestrictedMarkingTangent r p|) ≤ 2 * Real.log Z * M / y := by
  have hlogZ := Real.log_nonneg hZ
  calc
    _ ≤ ∑ p ∈ P, (2 * Real.log Z) * (1 / (p : ℝ) ^ 2) := by
      apply sum_le_sum
      intro p hp
      have hp₀ : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      have hl := Real.log_nonneg (by exact_mod_cast (hP p hp).one_lt.le : (1 : ℝ) ≤ p)
      unfold cubicSieveRestrictedMarkingTangent
      split_ifs
      · simp only [abs_zero]
        positivity
      · rw [abs_of_nonneg (by positivity : 0 ≤ 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2)]
        exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.log_le_log hp₀ (hmax p hp)) (by norm_num)) (sq_nonneg _)).trans_eq (by ring)
    _ = (2 * Real.log Z) * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (cubicSieve_markingSquareMass_le P hy hmin hmass)
      (mul_nonneg (by norm_num) hlogZ)).trans_eq (by ring)

end ArtinMatthews
