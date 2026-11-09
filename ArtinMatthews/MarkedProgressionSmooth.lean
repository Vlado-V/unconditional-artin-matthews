module

public import ArtinMatthews.MarkedProgressionCounting
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts


set_option backward.privateInPublic true
@[expose] public section

/-!
# Smooth summation from an explicit progression-count discrepancy

Abel summation turns the already proved uniform residue-count error into
a smooth-test error controlled by total variation. This is the analytic
smoothing step used for individual represented divisors in Lemma 7.2 of
the prime-predecessor paper. The coefficient-prefix hypothesis below is
an explicit finite-count bound, not the desired summed marked estimate.
-/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

/-- Smooth summation with the prefix discrepancy kept explicit. -/
theorem marked_smooth_sum_error (c : ℕ → ℝ) (f : ℝ → ℝ)
    {T ρ E : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0)
    (hprefix : ∀ t ∈ Set.Ioc 0 T,
      |(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) - ρ * t| ≤ E) :
    |(∑ k ∈ Finset.Icc 0 ⌊T⌋₊, f k * c k) - ρ * ∫ t in Set.Ioc 0 T, f t| ≤
      E * ∫ t in Set.Ioc 0 T, |deriv f t| := by
  have hfi : IntegrableOn (deriv f) (Set.Icc 0 T) := hderiv.continuousOn.integrableOn_Icc
  have hab := sum_mul_eq_sub_integral_mul c hT (fun t _ => hf t) hfi
  rw [hfT, zero_mul, zero_sub] at hab
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (u' := fun _ => (1 : ℝ)) (v := f) (v' := deriv f)
    (a := 0) (b := T) (fun t _ => hasDerivAt_id t) (fun t _ => (hf t).hasDerivAt)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 T)
    (hderiv.intervalIntegrable 0 T)
  simp only [hfT, mul_zero, zero_mul, sub_zero, one_mul, zero_sub] at hp
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT] at hp
  have hmain : (∫ t in Set.Ioc 0 T, deriv f t * t) = -(∫ t in Set.Ioc 0 T, f t) := by
    simpa only [mul_comm] using hp
  have hA : IntegrableOn (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)
      (Set.Ioc 0 T) :=
    (integrableOn_mul_sum_Icc c (a := 0) (b := T) (m := 0) le_rfl hfi).mono_set
      Set.Ioc_subset_Icc_self
  have ht : IntegrableOn (fun t => deriv f t * t) (Set.Ioc 0 T) :=
    (hderiv.mul continuous_id).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have herror : (∑ k ∈ Finset.Icc 0 ⌊T⌋₊, f k * c k) - ρ * ∫ t in Set.Ioc 0 T, f t =
      -(∫ t in Set.Ioc 0 T,
        deriv f t * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) - ρ * t)) := by
    rw [hab]
    simp_rw [mul_sub, show ∀ t : ℝ, deriv f t * (ρ * t) = ρ * (deriv f t * t) by intro t; ring]
    rw [integral_sub hA (ht.const_mul ρ), integral_const_mul, hmain]
    ring
  rw [herror, abs_neg]
  have hbound : IntegrableOn (fun t => E * |deriv f t|) (Set.Ioc 0 T) :=
    (continuous_const.mul hderiv.abs).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hi := norm_integral_le_of_norm_le
    (f := fun t => deriv f t * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) - ρ * t))
    hbound (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [Real.norm_eq_abs]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hprefix t ht) (abs_nonneg _)).trans_eq (mul_comm _ _))
  simpa only [Real.norm_eq_abs, integral_const_mul] using hi

/-- Uniform real-prefix discrepancy, including the possible integer zero. -/
theorem marked_residue_prefix_error (q a : ℕ) (hq : 0 < q) {t : ℝ} (ht : 0 ≤ t) :
    |(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, if Nat.ModEq q k a then (1 : ℝ) else 0) - t / q| ≤ 3 := by
  classical
  have hcount := marked_interval_residue_error 0 ⌊t⌋₊ q a (Nat.zero_le _) hq
  have hsum : (∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, if Nat.ModEq q k a then (1 : ℝ) else 0) =
      (((Finset.Ioc 0 ⌊t⌋₊).filter (fun k => Nat.ModEq q k a)).card : ℝ) := by simp
  rw [← hsum] at hcount
  simp only [Nat.cast_zero, sub_zero] at hcount
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hfloor : |(⌊t⌋₊ : ℝ) - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Nat.floor_le ht, Nat.lt_floor_add_one t]
  have hround : |(⌊t⌋₊ : ℝ) / q - t / q| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hqR]
    exact (div_le_one hqR).mpr (hfloor.trans hq1)
  have hzero : |(if Nat.ModEq q 0 a then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  have heq :
      (if Nat.ModEq q 0 a then (1 : ℝ) else 0) +
        (∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, if Nat.ModEq q k a then (1 : ℝ) else 0) - t / q =
      (if Nat.ModEq q 0 a then (1 : ℝ) else 0) +
        ((∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, if Nat.ModEq q k a then (1 : ℝ) else 0) - (⌊t⌋₊ : ℝ) / q) +
        ((⌊t⌋₊ : ℝ) / q - t / q) := by ring
  rw [heq]
  have hzS := abs_add_le
    (if Nat.ModEq q 0 a then (1 : ℝ) else 0)
    ((∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, if Nat.ModEq q k a then (1 : ℝ) else 0) - (⌊t⌋₊ : ℝ) / q)
  have hS := abs_add_le
    ((if Nat.ModEq q 0 a then (1 : ℝ) else 0) +
      ((∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, if Nat.ModEq q k a then (1 : ℝ) else 0) - (⌊t⌋₊ : ℝ) / q))
    ((⌊t⌋₊ : ℝ) / q - t / q)
  linarith

/-- A smooth progression sum has an absolute error controlled solely by
three times the test function's total variation, uniformly in both moduli. -/
theorem marked_divisor_smooth_error (d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) :
    |(∑ k ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun k => d ∣ k ∧ r ∣ k + 1), f k) -
      (if d.Coprime r then (∫ t in Set.Ioc 0 T, f t) / (d * r : ℕ) else 0)| ≤
      3 * ∫ t in Set.Ioc 0 T, |deriv f t| := by
  classical
  by_cases hcop : d.Coprime r
  · obtain ⟨a, _ha, hclass⟩ := marked_divisor_crt hd hr hcop
    have h := marked_smooth_sum_error
      (fun k => if d ∣ k ∧ r ∣ k + 1 then (1 : ℝ) else 0) f
      (ρ := 1 / (d * r : ℕ)) (E := 3) hT hf hderiv hfT (by
        intro t ht
        have he := marked_residue_prefix_error (d * r) a (Nat.mul_pos hd hr) ht.1.le
        simpa only [hclass, div_eq_mul_inv, one_mul, mul_one, mul_comm] using he)
    rw [ite_eq_left hcop]
    simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero, div_eq_mul_inv, one_mul, mul_comm] using h
  · have hnone : ∀ k : ℕ, ¬ (d ∣ k ∧ r ∣ k + 1) := fun k h => hcop (marked_divisor_coprime h.1 h.2)
    have hzero : (Finset.Icc 0 ⌊T⌋₊).filter (fun k => d ∣ k ∧ r ∣ k + 1) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      exact fun k _ => hnone k
    rw [hzero, Finset.sum_empty, ite_eq_right hcop]
    have hi : 0 ≤ ∫ t in Set.Ioc 0 T, |deriv f t| := integral_nonneg (fun t => abs_nonneg _)
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hi

end ArtinMatthews
