module

public import ArtinMatthews.CubicSieveJointEuler
public import ArtinMatthews.CubicSieveAbsoluteModelMass


set_option backward.privateInPublic true
@[expose] public section

/-! Value and tangent comparison for the literal retained Euler sum.
Only its negligible marking errors use absolute coefficient masses. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_correctionModel_hasDerivAt_one (z : ℝ) (m : ℕ) :
    HasDerivAt (cubicSieveDivisorCorrectionModel z m)
      (∑ R ∈ (Nat.primesLE ⌊z⌋₊).powerset,
        cubicSieveCorrectionCoeff z m R * (-cubicSieveDivisorLogMoment (roughSubsetDivisor R))) 1 := by
  have heq : cubicSieveDivisorCorrectionModel z m = fun s =>
      ∑ R ∈ (Nat.primesLE ⌊z⌋₊).powerset,
        cubicSieveCorrectionCoeff z m R * cubicSieveDivisorFactor (roughSubsetDivisor R) s :=
    funext (cubicSieve_correctionModel_eq_divisorFactor z m)
  rw [heq]
  apply HasDerivAt.fun_sum
  intro R hR
  convert! (cubicSieve_divisorFactor_hasDerivAt_one (roughSubsetDivisor_pos R
    (fun p hp => Nat.prime_of_mem_primesLE (mem_powerset.mp hR hp)))).const_mul
      (cubicSieveCorrectionCoeff z m R) using 1

theorem cubicSieve_jointEuler_value_compare {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (z : ℝ) (m k : ℕ) (μ E : ℝ)
    (hval : ∀ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S ≠ 0 →
      |cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor S) 1 - μ| ≤ E) :
    |cubicSieveJointEulerModel P V z m k 1 - μ * cubicSieveDivisorCorrectionModel z m 1| ≤
      cubicSieveCorrectionAbsoluteMass z m * E := by
  have heq : cubicSieveJointEulerModel P V z m k 1 - μ * cubicSieveDivisorCorrectionModel z m 1 =
      ∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset,
        cubicSieveCorrectionCoeff z m S * cubicSieveDivisorFactor (roughSubsetDivisor S) 1 *
          (cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor S) 1 - μ) := by
    rw [cubicSieve_correctionModel_eq_divisorFactor]
    unfold cubicSieveJointEulerModel
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro S _
    ring
  rw [heq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  unfold cubicSieveCorrectionAbsoluteMass
  rw [sum_mul]
  apply sum_le_sum
  intro S hS
  by_cases hc : cubicSieveCorrectionCoeff z m S = 0
  · simp only [hc, zero_mul, abs_zero, le_refl]
  have hp (p : ℕ) (hp : p ∈ S) := Nat.prime_of_mem_primesLE (mem_powerset.mp hS hp)
  have hg := cubicSieve_divisorFactor_one_nonneg (roughSubsetDivisor_squarefree S hp)
  rw [abs_mul, abs_mul, abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_left (hval S hS hc) (mul_nonneg (abs_nonneg _) hg)

theorem cubicSieve_jointEuler_tangent_compare {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (z : ℝ) (m k : ℕ) (μ E : ℝ)
    (hval : ∀ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S ≠ 0 →
      |cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor S) 1 - μ| ≤ E)
    (htan : ∀ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S ≠ 0 →
      |deriv (cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor S)) 1| ≤ E) :
    |deriv (cubicSieveJointEulerModel P V z m k) 1 - μ * deriv (cubicSieveDivisorCorrectionModel z m) 1| ≤
      (cubicSieveCorrectionDerivativeMass z m + cubicSieveCorrectionAbsoluteMass z m) * E := by
  rw [(cubicSieve_jointEulerModel_hasDerivAt_one P V hP z m k).deriv,
    (cubicSieve_correctionModel_hasDerivAt_one z m).deriv]
  unfold cubicSieveJointEulerTangent
  rw [mul_sum, ← sum_sub_distrib]
  have heq : (∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset,
      (cubicSieveCorrectionCoeff z m S *
          (-cubicSieveDivisorLogMoment (roughSubsetDivisor S) * cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor S) 1 +
           cubicSieveDivisorLeading (roughSubsetDivisor S) * cubicSieveFirstArrayTruncationTangent P V
            (fun p => cubicSieveRestrictedMarkingDensity (roughSubsetDivisor S) p 1)
            (cubicSieveRestrictedMarkingTangent (roughSubsetDivisor S)) k) -
        μ * (cubicSieveCorrectionCoeff z m S * -cubicSieveDivisorLogMoment (roughSubsetDivisor S)))) =
      ∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset,
        cubicSieveCorrectionCoeff z m S *
          (-cubicSieveDivisorLogMoment (roughSubsetDivisor S) *
              (cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor S) 1 - μ) +
           cubicSieveDivisorFactor (roughSubsetDivisor S) 1 *
             deriv (cubicSieveFirstArrayEulerSum P V k (roughSubsetDivisor S)) 1) := by
    apply sum_congr rfl
    intro S hS
    rw [(cubicSieve_firstArrayEulerSum_hasDerivAt_one P V hP k (roughSubsetDivisor S)).deriv,
      cubicSieve_divisorFactor_one (roughSubsetDivisor_pos S
      (fun p hp => Nat.prime_of_mem_primesLE (mem_powerset.mp hS hp)))]
    ring
  rw [heq]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  unfold cubicSieveCorrectionDerivativeMass cubicSieveCorrectionAbsoluteMass
  rw [add_mul, sum_mul, sum_mul, ← sum_add_distrib]
  apply sum_le_sum
  intro S hS
  by_cases hc : cubicSieveCorrectionCoeff z m S = 0
  · simp only [hc, zero_mul, abs_zero, zero_add, le_refl]
  have hp (p : ℕ) (hp : p ∈ S) := Nat.prime_of_mem_primesLE (mem_powerset.mp hS hp)
  have hg := cubicSieve_divisorFactor_one_nonneg (roughSubsetDivisor_squarefree S hp)
  rw [abs_mul]
  refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)).trans ?_
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hg]
  exact (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (hval S hS hc) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (htan S hS hc) hg)) (abs_nonneg _)).trans_eq (by ring)

end ArtinMatthews
