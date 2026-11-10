module

public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The monomial moments of Mathlib's shifted Legendre polynomials. -/

namespace ArtinMatthews

open Polynomial
open scoped Polynomial

noncomputable section

private def legendreRodriguesPolynomial (n : ℕ) : ℤ[X] :=
  X ^ n * (1 - X) ^ n

private theorem legendreRodrigues_derivative_zero (n k : ℕ) (hk : k < n) :
    aeval (0 : ℝ) (derivative^[k] (legendreRodriguesPolynomial n)) = 0 := by
  rw [← coeff_zero_eq_aeval_zero', coeff_iterate_derivative, zero_add,
    legendreRodriguesPolynomial, coeff_X_pow_mul', if_neg (not_le_of_gt hk), smul_zero, map_zero]

private theorem legendreRodrigues_derivative_one (n k : ℕ) (hk : k < n) :
    aeval (1 : ℝ) (derivative^[k] (legendreRodriguesPolynomial n)) = 0 := by
  have hsymm : (legendreRodriguesPolynomial n).comp (1 - X) = legendreRodriguesPolynomial n := by
    simp only [legendreRodriguesPolynomial, mul_comp, pow_comp, X_comp, sub_comp, one_comp,
      sub_sub_cancel]
    rw [mul_comm]
  have he := congrArg (aeval (1 : ℝ))
    (iterate_derivative_comp_one_sub_X (legendreRodriguesPolynomial n) k)
  rw [hsymm] at he
  simpa only [map_mul, map_pow, map_neg, map_one, aeval_comp, map_sub, aeval_X, sub_self,
    legendreRodrigues_derivative_zero n k hk, mul_zero] using he

private theorem integral_aeval_mul_iterate_derivative (n : ℕ) (p q : ℤ[X])
    (hzero : ∀ k < n, aeval (0 : ℝ) (derivative^[k] q) = 0)
    (hone : ∀ k < n, aeval (1 : ℝ) (derivative^[k] q) = 0) :
    (∫ x in (0 : ℝ)..1, aeval x p * aeval x (derivative^[n] q)) =
      (-1 : ℝ)^n * (∫ x in (0 : ℝ)..1, aeval x (derivative^[n] p) * aeval x q) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    have hp' : Continuous (fun x : ℝ => aeval x (derivative p)) :=
      (derivative p).differentiable_aeval.continuous
    have hq' : Continuous (fun x : ℝ => aeval x (derivative (derivative^[n] q))) :=
      (derivative (derivative^[n] q)).differentiable_aeval.continuous
    have hparts :
        (∫ x in (0 : ℝ)..1, aeval x p * aeval x (derivative (derivative^[n] q))) =
          -(∫ x in (0 : ℝ)..1, aeval x (derivative p) * aeval x (derivative^[n] q)) := by
      simpa only [hzero n (Nat.lt_succ_self n), hone n (Nat.lt_succ_self n),
        mul_zero, sub_self, zero_sub] using
        intervalIntegral.integral_mul_deriv_eq_deriv_mul
          (fun x _ => p.hasDerivAt_aeval x)
          (fun x _ => (derivative^[n] q).hasDerivAt_aeval x)
          (hp'.intervalIntegrable 0 1) (hq'.intervalIntegrable 0 1)
    rw [Function.iterate_succ_apply' derivative n q, hparts,
      ih (derivative p) (fun k hk => hzero k (Nat.lt_succ_of_lt hk))
        (fun k hk => hone k (Nat.lt_succ_of_lt hk)),
      Function.iterate_succ_apply derivative n p, pow_succ]
    ring

private theorem integral_pow_one_sub_pow_step (m n : ℕ) :
    ((m : ℝ) + 1) * (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ (n + 1)) =
      ((n : ℝ) + 1) * (∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ n) := by
  have hu (x : ℝ) : HasDerivAt (fun y : ℝ => (1 - y) ^ (n + 1))
      (-((n : ℝ) + 1) * (1 - x) ^ n) x := by
    have hlin : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x :=
      (hasDerivAt_id x).const_sub 1
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_neg, mul_one, neg_mul] using
      hlin.fun_pow (n + 1)
  have hv (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ (m + 1)) (((m : ℝ) + 1) * x ^ m) x := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hasDerivAt_pow (m + 1) x
  have hu' : Continuous (fun x : ℝ => -((n : ℝ) + 1) * (1 - x) ^ n) := by fun_prop
  have hv' : Continuous (fun x : ℝ => ((m : ℝ) + 1) * x ^ m) := by fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hu x) (fun x _ => hv x)
    (hu'.intervalIntegrable 0 1) (hv'.intervalIntegrable 0 1)
  have hleft (x : ℝ) : (1 - x) ^ (n + 1) * (((m : ℝ) + 1) * x ^ m) =
      ((m : ℝ) + 1) * (x ^ m * (1 - x) ^ (n + 1)) := by ring
  have hright (x : ℝ) : (-((n : ℝ) + 1) * (1 - x) ^ n) * x ^ (m + 1) =
      -((n : ℝ) + 1) * (x ^ (m + 1) * (1 - x) ^ n) := by ring
  simp only [hleft, hright, intervalIntegral.integral_const_mul] at hparts
  simpa only [sub_self, sub_zero,
    zero_pow (Nat.succ_ne_zero _), zero_mul, mul_zero, zero_sub, neg_mul, neg_neg] using hparts

private theorem integral_pow_one_sub_pow (m n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ n) =
      (m.factorial : ℝ) * (n.factorial : ℝ) / ((m + n + 1).factorial : ℝ) := by
  induction n generalizing m with
  | zero =>
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Nat.add_zero,
      integral_pow, one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have hmf : (m.factorial : ℝ) ≠ 0 := by positivity
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp <;> norm_num
  | succ n ih =>
    apply mul_left_cancel₀ (a := (m : ℝ) + 1) (by positivity)
    rw [integral_pow_one_sub_pow_step, ih (m + 1)]
    have harg : m + 1 + n + 1 = m + (n + 1) + 1 := by omega
    rw [harg, Nat.factorial_succ m, Nat.factorial_succ n]
    simp only [Nat.cast_mul, Nat.cast_succ]
    ring

theorem integral_pow_shiftedLegendre (n m : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ m * aeval x (shiftedLegendre n)) =
      (-1 : ℝ) ^ n * ((m.descFactorial n * m.factorial : ℕ) : ℝ) /
        ((m + n + 1).factorial : ℝ) := by
  have hRodrigues :
      (n.factorial : ℝ) * (∫ x in (0 : ℝ)..1, x ^ m * aeval x (shiftedLegendre n)) =
        ∫ x in (0 : ℝ)..1, aeval x (X ^ m : ℤ[X]) *
          aeval x (derivative^[n] (legendreRodriguesPolynomial n)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    have he := congrArg (aeval x) (factorial_mul_shiftedLegendre_eq n)
    change aeval x ((n.factorial : ℤ[X]) * shiftedLegendre n) =
      aeval x (derivative^[n] (legendreRodriguesPolynomial n)) at he
    rw [map_mul, map_natCast] at he
    change (n.factorial : ℝ) * (x ^ m * aeval x (shiftedLegendre n)) =
      aeval x (X ^ m : ℤ[X]) * aeval x (derivative^[n] (legendreRodriguesPolynomial n))
    rw [map_pow, aeval_X, ← he]
    ring
  have hparts := integral_aeval_mul_iterate_derivative n (X ^ m : ℤ[X])
    (legendreRodriguesPolynomial n) (legendreRodrigues_derivative_zero n)
    (legendreRodrigues_derivative_one n)
  have hmonomial :
      (fun x : ℝ => aeval x (derivative^[n] (X ^ m : ℤ[X])) *
        aeval x (legendreRodriguesPolynomial n)) =
      fun x => (m.descFactorial n : ℝ) * (x ^ m * (1 - x) ^ n) := by
    funext x
    simp only [iterate_derivative_X_pow_eq_natCast_mul, legendreRodriguesPolynomial,
      map_mul, map_natCast, map_pow, aeval_X, map_sub, map_one]
    by_cases hnm : n ≤ m
    · calc
        _ = (m.descFactorial n : ℝ) * (x ^ ((m - n) + n) * (1 - x) ^ n) := by
          rw [pow_add]
          ring
        _ = _ := by rw [Nat.sub_add_cancel hnm]
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr (lt_of_not_ge hnm), Nat.cast_zero, zero_mul]
  apply mul_left_cancel₀ (a := (n.factorial : ℝ)) (by positivity)
  rw [hRodrigues, hparts, hmonomial, intervalIntegral.integral_const_mul,
    integral_pow_one_sub_pow, Nat.cast_mul]
  ring

end

end ArtinMatthews
