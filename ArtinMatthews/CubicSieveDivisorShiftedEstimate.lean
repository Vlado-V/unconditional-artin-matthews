module

public import ArtinMatthews.CubicSieveDivisorUnitEstimate


set_option backward.privateInPublic true
@[expose] public section

/-! The reduced-class floor estimates summed with the exact squarefree
Euler coefficients, retaining the signed main term. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveShiftedDivisorMain (d r X : ℕ) : ℝ :=
  ∑ T ∈ r.primeFactors.powerset, cubicSieveDivisorEulerCoeff r.primeFactors T *
    cubicSieveDivisorUnitMain d (X / (r * roughSubsetDivisor T))

theorem cubicSieve_divisorEulerCoeff_abs_sum (P : Finset ℕ) :
    (∑ T ∈ P.powerset, |cubicSieveDivisorEulerCoeff P T|) = (3 : ℝ) ^ P.card := by
  calc
    _ = ∑ T ∈ P.powerset, (∏ _p ∈ T, (1 : ℝ)) * ∏ _p ∈ P \ T, (2 : ℝ) := by
      apply sum_congr rfl
      intro T hT
      unfold cubicSieveDivisorEulerCoeff
      rw [abs_prod]
      simp only [apply_ite, abs_neg, abs_one, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [prod_ite, filter_mem_eq_inter, inter_eq_right.mpr (mem_powerset.mp hT),
        filter_notMem_eq_sdiff]
    _ = _ := by
      rw [← prod_add]
      norm_num

theorem cubicSieve_shiftedDivisorProgression_count_error {d r X : ℕ}
    (hd : 0 < d) (hr : Squarefree r) (hc : d.Coprime r) :
    |cubicSieveShiftedDivisorProgression d r X (fun _ => 1) -
      cubicSieveShiftedDivisorMain d r X| ≤
      ∑ T ∈ r.primeFactors.powerset, |cubicSieveDivisorEulerCoeff r.primeFactors T| *
        (5 * ((X / (r * roughSubsetDivisor T)).sqrt : ℝ)) := by
  rw [cubicSieve_shiftedDivisorProgression_expand hr, cubicSieveShiftedDivisorMain,
    ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  apply sum_le_sum
  intro T hT
  let a := r * roughSubsetDivisor T
  let N := X / a
  have hsub := mem_powerset.mp hT
  have ha : 0 < a := Nat.mul_pos (Nat.pos_of_ne_zero hr.ne_zero)
    (roughSubsetDivisor_pos T (fun _ hp => Nat.prime_of_mem_primeFactors (hsub hp)))
  have hcop : a.Coprime d := cubicSieve_divisorShift_coprime_modulus hc hsub
  let v : (ZMod d)ˣ := (ZMod.unitOfCoprime a hcop)⁻¹ * 1
  have hclass (k : ℕ) (hk : 0 < k) :
      d ∣ a * k - 1 ↔ (k : ZMod d) = (v : ZMod d) := by
    rw [cubicSieve_shifted_residue_iff (Nat.mul_pos ha hk), ← ZMod.natCast_eq_natCast_iff,
      Nat.cast_one]
    exact cubicSieve_unit_progression_quotient hcop 1 k
  have hI : Ioc 0 N = Icc 1 N := by
    ext k
    simp only [mem_Ioc, mem_Icc]
    omega
  have hcount :
      (∑ k ∈ Ioc 0 N, if d ∣ a * k - 1 then (k.divisors.card : ℝ) * 1 else 0) =
        cubicSieveDivisorUnitCount d N v := by
    rw [cubicSieveDivisorUnitCount, hI]
    apply sum_congr rfl
    intro k hk
    simp only [hclass k (mem_Icc.mp hk).1, mul_one, mul_ite, mul_zero]
  change |cubicSieveDivisorEulerCoeff r.primeFactors T *
      (∑ k ∈ Ioc 0 N, if d ∣ a * k - 1 then (k.divisors.card : ℝ) * 1 else 0) -
      cubicSieveDivisorEulerCoeff r.primeFactors T * cubicSieveDivisorUnitMain d N| ≤ _
  rw [hcount, ← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (cubicSieve_divisorUnitCount_error d N hd v) (abs_nonneg _)

theorem cubicSieve_shiftedDivisorProgression_count_error_uniform {d r X : ℕ}
    (hd : 0 < d) (hr : Squarefree r) (hc : d.Coprime r) :
    |cubicSieveShiftedDivisorProgression d r X (fun _ => 1) -
      cubicSieveShiftedDivisorMain d r X| ≤
      (3 : ℝ) ^ r.primeFactors.card * (5 * ((X / r).sqrt : ℝ)) := by
  apply (cubicSieve_shiftedDivisorProgression_count_error hd hr hc).trans
  rw [← cubicSieve_divisorEulerCoeff_abs_sum, sum_mul]
  apply sum_le_sum
  intro T hT
  have hTpos := roughSubsetDivisor_pos T
    (fun _ hp => Nat.prime_of_mem_primeFactors (mem_powerset.mp hT hp))
  have hle : X / (r * roughSubsetDivisor T) ≤ X / r :=
    Nat.div_le_div_left (Nat.le_mul_of_pos_right r hTpos) (Nat.pos_of_ne_zero hr.ne_zero)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sqrt_le_sqrt hle)) (by norm_num))
    (abs_nonneg _)

end ArtinMatthews
