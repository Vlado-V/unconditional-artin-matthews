module

public import ArtinMatthews.MarkedProgressionExpansion
public import ArtinMatthews.GiantCandidateSquareCount
public import Mathlib.Algebra.BigOperators.Ring.Finset


set_option backward.privateInPublic true
@[expose] public section

/-! Exponential moments of the actual distinct hits in the combined bands. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem sourceComparisonMultiples_card (d N : ℕ) :
    ((Ioc 0 N).filter (fun n => d ∣ n)).card = N / d := by
  classical
  have he : (Ioc 0 N).filter (fun n => d ∣ n) =
      (range (N + 1)).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_range, Nat.lt_succ_iff, Nat.pos_iff_ne_zero]
    tauto
  rw [he, Nat.card_multiples']

theorem sourceComparisonHitMoment_expansion (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (B : ℝ) (n : ℕ) :
    B ^ bandCount P n =
      ∑ S ∈ P.powerset, if (∏ p ∈ S, p) ∣ n then (B - 1) ^ S.card else 0 := by
  classical
  have he (p : ℕ) :
      (if p ∣ n then B else 1) = 1 + (B - 1) * (if p ∣ n then 1 else 0) := by
    split_ifs <;> ring
  calc
    _ = ∏ p ∈ P, (if p ∣ n then B else 1) := by
      rw [← prod_filter, prod_const, bandCount, activeDivisors]
    _ = ∏ p ∈ P, (1 + (B - 1) * (if p ∣ n then 1 else 0)) :=
      prod_congr rfl (fun p _ => he p)
    _ = ∑ S ∈ P.powerset, ∏ p ∈ S, ((B - 1) * (if p ∣ n then 1 else 0)) :=
      prod_one_add P
    _ = _ := sum_congr rfl (fun S hS =>
      marked_hit_product S (fun p hp => hP p (mem_powerset.mp hS hp)) n (B - 1))

theorem sourceComparisonHitMoment_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {B : ℝ} (hB : 1 ≤ B) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, B ^ bandCount P n) ≤
      (N : ℝ) * Real.exp ((B - 1) * ∑ p ∈ P, 1 / (p : ℝ)) := by
  classical
  simp_rw [sourceComparisonHitMoment_expansion P hP B]
  rw [sum_comm]
  calc
    _ ≤ ∑ S ∈ P.powerset, (N : ℝ) * ∏ p ∈ S, ((B - 1) / (p : ℝ)) := by
      apply sum_le_sum
      intro S _
      rw [← sum_filter, sum_const, nsmul_eq_mul, sourceComparisonMultiples_card]
      have hd : ((N / (∏ p ∈ S, p) : ℕ) : ℝ) ≤ (N : ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) :=
        Nat.cast_div_le
      calc
        _ ≤ ((N : ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ)) * (B - 1) ^ S.card :=
          mul_le_mul_of_nonneg_right hd (pow_nonneg (sub_nonneg.mpr hB) _)
        _ = _ := by rw [prod_div_distrib, Nat.cast_prod, prod_const]; ring
    _ = (N : ℝ) * ∏ p ∈ P, (1 + (B - 1) / (p : ℝ)) := by
      rw [← mul_sum, prod_one_add]
    _ ≤ (N : ℝ) * ∏ p ∈ P, Real.exp ((B - 1) / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply prod_le_prod₀
      · intro p _
        exact add_nonneg zero_le_one (div_nonneg (sub_nonneg.mpr hB) (Nat.cast_nonneg _))
      · intro p _
        simpa only [add_comm (1 : ℝ)] using Real.add_one_le_exp ((B - 1) / (p : ℝ))
    _ = _ := by
      rw [← Real.exp_sum, mul_sum]
      congr 2
      apply sum_congr rfl
      intro p _
      ring

end
end ArtinMatthews
