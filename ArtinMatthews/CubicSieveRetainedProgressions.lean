module

public import ArtinMatthews.CubicSieveCorrection
public import ArtinMatthews.CubicSieveDivisorSourceWeight
public import ArtinMatthews.CubicSamplingArrayTruncation


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signed progression expansion of the retained Section 7 sum. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveRetainedWeightedSum {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (Φ : ℝ → ℝ) (z x : ℝ) (m k : ℕ) : ℝ :=
  ∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) *
    cubicSamplingArrayTruncation P V (fun _ => 1) k u *
    (u + 1).divisors.card * cubicSieveCorrection z m (u + 1)

theorem cubicSieve_retainedRow_eq_progressions {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (Φ : ℝ → ℝ) (x : ℝ) (k r : ℕ) :
    (∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) *
      cubicSamplingArrayTruncation P V (fun _ => 1) k u *
      (u + 1).divisors.card * (if r ∣ u + 1 then 1 else 0)) =
    ∑ t ∈ representedArrayChoices P (fun _ => 1),
      ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
        (representedArrayCoefficient V (fun _ => 1) t *
          markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i) *
        ∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) *
          cubicSieveShiftedDivisorCoefficient (markedWeightedDivisor (representedArraySelected t) i) r (u + 1) := by
  simp_rw [cubicSampling_arrayTruncation_eq_divisors, mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro u _
  unfold cubicSieveShiftedDivisorCoefficient
  simp only [Nat.add_sub_cancel]
  by_cases hd : markedWeightedDivisor (representedArraySelected t) i ∣ u
  · by_cases hr : r ∣ u + 1
    · simp only [hd, hr, ite_true, and_self, mul_one]
      ring
    · simp [hd, hr]
  · simp [hd]

theorem cubicSieve_retainedWeightedSum_eq_progressions {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (Φ : ℝ → ℝ) (z x : ℝ) (m k : ℕ) :
    cubicSieveRetainedWeightedSum P V Φ z x m k =
      ∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S *
        ∑ t ∈ representedArrayChoices P (fun _ => 1),
          ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
            (representedArrayCoefficient V (fun _ => 1) t *
              markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i) *
            ∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) *
              cubicSieveShiftedDivisorCoefficient (markedWeightedDivisor (representedArraySelected t) i)
                (roughSubsetDivisor S) (u + 1) := by
  have hsplit : cubicSieveRetainedWeightedSum P V Φ z x m k =
      ∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S *
        ∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) *
          cubicSamplingArrayTruncation P V (fun _ => 1) k u *
          (u + 1).divisors.card * (if roughSubsetDivisor S ∣ u + 1 then 1 else 0) := by
    unfold cubicSieveRetainedWeightedSum
    simp_rw [cubicSieve_correction_eq_divisor_sum, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro S _
    apply sum_congr rfl
    intro u _
    split_ifs <;> ring
  rw [hsplit]
  apply sum_congr rfl
  intro S _
  rw [cubicSieve_retainedRow_eq_progressions]

theorem cubicSieve_shiftedDivisorCoefficient_zero_of_not_coprime {d r : ℕ}
    (hc : ¬d.Coprime r) (u : ℕ) : cubicSieveShiftedDivisorCoefficient d r (u + 1) = 0 := by
  unfold cubicSieveShiftedDivisorCoefficient
  simp only [Nat.add_sub_cancel]
  split_ifs with h
  · exact (hc (Nat.Coprime.of_dvd h.2 h.1 (by simp))).elim
  · rfl

end ArtinMatthews
