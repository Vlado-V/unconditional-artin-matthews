module

public import ArtinMatthews.CubicSieveJointEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The actual logarithmic progression densities are the value and
first derivative of the same retained Euler polynomial. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_jointEuler_eq_progressionFactors {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (z : ℝ) (m k : ℕ) (s : ℝ) :
    cubicSieveJointEulerModel P V z m k s =
      ∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S *
        ∑ t ∈ representedArrayChoices P (fun _ => 1),
          ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
            (representedArrayCoefficient V (fun _ => 1) t *
              markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i) *
            (if (markedWeightedDivisor (representedArraySelected t) i).Coprime (roughSubsetDivisor S) then
              cubicSieveProgressionEulerFactor (markedWeightedDivisor (representedArraySelected t) i)
                (roughSubsetDivisor S) s else 0) := by
  unfold cubicSieveJointEulerModel cubicSieveFirstArrayEulerSum
  apply sum_congr rfl
  intro S _
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  unfold cubicSieveProgressionEulerFactor
  split_ifs <;> ring

def cubicSieveJointPoleTangent {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (z : ℝ) (m k : ℕ) : ℝ :=
  ∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S *
    ∑ t ∈ representedArrayChoices P (fun _ => 1),
      ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
        (representedArrayCoefficient V (fun _ => 1) t *
          markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i) *
        (if (markedWeightedDivisor (representedArraySelected t) i).Coprime (roughSubsetDivisor S) then
          deriv (cubicSieveProgressionEulerFactor (markedWeightedDivisor (representedArraySelected t) i)
            (roughSubsetDivisor S)) 1 else 0)

theorem cubicSieve_jointEuler_hasDerivAt_pole {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (z : ℝ) (m k : ℕ) :
    HasDerivAt (cubicSieveJointEulerModel P V z m k) (cubicSieveJointPoleTangent P V z m k) 1 := by
  have heq : cubicSieveJointEulerModel P V z m k = fun s =>
      ∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S *
        ∑ t ∈ representedArrayChoices P (fun _ => 1),
          ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
            (representedArrayCoefficient V (fun _ => 1) t *
              markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i) *
            (if (markedWeightedDivisor (representedArraySelected t) i).Coprime (roughSubsetDivisor S) then
              cubicSieveProgressionEulerFactor (markedWeightedDivisor (representedArraySelected t) i)
                (roughSubsetDivisor S) s else 0) :=
    funext (cubicSieve_jointEuler_eq_progressionFactors P V z m k)
  rw [heq]
  unfold cubicSieveJointPoleTangent
  apply HasDerivAt.fun_sum
  intro S hS
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro t ht
  apply HasDerivAt.fun_sum
  intro i hi
  apply HasDerivAt.const_mul
  have hr := roughSubsetDivisor_pos S (fun p hp => Nat.prime_of_mem_primesLE (mem_powerset.mp hS hp))
  have hd := markedWeightedDivisor_pos (univ.biUnion P) (representedArraySelected t)
    (fun p hp => by obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp; exact hP j p hp)
    (cubicSampling_selected_subset P (fun _ => 1) ht) hi
  by_cases hc : (markedWeightedDivisor (representedArraySelected t) i).Coprime (roughSubsetDivisor S)
  · have hdiff : DifferentiableAt ℝ (cubicSieveProgressionEulerFactor
        (markedWeightedDivisor (representedArraySelected t) i) (roughSubsetDivisor S)) 1 :=
      by convert! ((cubicSieve_divisorFactor_hasDerivAt_one hr).mul
        (cubicSieve_markingFactor_hasDerivAt_one hd)).differentiableAt using 1
    simpa only [ite_eq_left hc] using hdiff.hasDerivAt
  · simpa only [ite_eq_right hc] using hasDerivAt_const (1 : ℝ) (0 : ℝ)

theorem cubicSieve_jointPoleDensity {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (z : ℝ) (m k : ℕ) {u : ℝ} (hu : 0 < u) :
    (∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S *
      ∑ t ∈ representedArrayChoices P (fun _ => 1),
        ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
          (representedArrayCoefficient V (fun _ => 1) t *
            markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i) *
          (if (markedWeightedDivisor (representedArraySelected t) i).Coprime (roughSubsetDivisor S) then
            cubicSieveShiftedDivisorLogDensity (markedWeightedDivisor (representedArraySelected t) i)
              (roughSubsetDivisor S) u else 0)) =
      (Real.log u + 2 * Real.eulerMascheroniConstant) * cubicSieveJointEulerModel P V z m k 1 +
        deriv (cubicSieveJointEulerModel P V z m k) 1 := by
  rw [cubicSieve_jointEuler_eq_progressionFactors,
    (cubicSieve_jointEuler_hasDerivAt_pole P V hP z m k).deriv]
  unfold cubicSieveJointPoleTangent
  simp_rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro S hS
  have hr := roughSubsetDivisor_pos S (fun p hp => Nat.prime_of_mem_primesLE (mem_powerset.mp hS hp))
  apply sum_congr rfl
  intro t ht
  apply sum_congr rfl
  intro i hi
  have hd := markedWeightedDivisor_pos (univ.biUnion P) (representedArraySelected t)
    (fun p hp => by obtain ⟨j, _, hp⟩ := mem_biUnion.mp hp; exact hP j p hp)
    (cubicSampling_selected_subset P (fun _ => 1) ht) hi
  by_cases hc : (markedWeightedDivisor (representedArraySelected t) i).Coprime (roughSubsetDivisor S)
  · simp only [ite_eq_left hc, cubicSieve_shiftedDivisorLogDensity_eq_value_derivative hd hr hu]
    ring
  · simp only [ite_eq_right hc, mul_zero, zero_add]

end ArtinMatthews
