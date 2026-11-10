module

public import ArtinMatthews.MarkedTypeIICoefficients
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Actual factor-count and divisor-count bounds on rough integers, with
prime factors counted with multiplicity as required in prime extraction. -/

namespace ArtinMatthews

open Filter
open scoped BigOperators

theorem prime_extraction_list_lower_pow (l : List ℕ) {z : ℝ} (hz : 0 ≤ z)
    (hl : ∀ p ∈ l, z ≤ (p : ℝ)) : z ^ l.length ≤ (l.prod : ℝ) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.length_cons, pow_succ, List.prod_cons, Nat.cast_mul]
    calc
      z ^ l.length * z ≤ (l.prod : ℝ) * p := mul_le_mul
        (ih (fun q hq => hl q (List.mem_cons_of_mem p hq))) (hl p List.mem_cons_self)
        hz (Nat.cast_nonneg _)
      _ = _ := mul_comm _ _

/-- Roughness forces the total number of prime factors below the exponent
ratio. Repeated factors remain in the actual primeFactorsList. -/
theorem marked_rough_factor_count {n : ℕ} (hn : n ≠ 0) {x γ A : ℝ}
    (hx : 1 < x) (hγ : 0 < γ) (hnx : (n : ℝ) ≤ x ^ A)
    (hrough : MarkedRoughAbove (x ^ γ) n) :
    (n.primeFactorsList.length : ℝ) ≤ A / γ := by
  have hx0 : 0 ≤ x := by linarith
  have hprod := prime_extraction_list_lower_pow n.primeFactorsList
    (Real.rpow_nonneg hx0 γ) (fun p hp =>
      (hrough p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)).le)
  rw [Nat.prod_primeFactorsList hn] at hprod
  have hpow : x ^ (γ * (n.primeFactorsList.length : ℝ)) ≤ x ^ A := by
    rw [Real.rpow_mul hx0, Real.rpow_natCast]
    exact hprod.trans hnx
  have he := (Real.rpow_le_rpow_left_iff hx).mp hpow
  exact (le_div_iff₀ hγ).mpr (by nlinarith)

theorem prime_extraction_divisor_count_le {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤ 2 ^ n.primeFactorsList.length := by
  have hs : (∑ p ∈ n.primeFactors, n.factorization p) = n.primeFactorsList.length := by
    simpa only [Finsupp.sum, Nat.support_factorization, ArithmeticFunction.cardFactors_apply] using
      (ArithmeticFunction.cardFactors_eq_sum_factorization (n := n)).symm
  rw [Nat.card_divisors hn]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1)) ≤
        ∏ p ∈ n.primeFactors, 2 ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => Nat.succ_le_of_lt Nat.lt_two_pow_self)
    _ = 2 ^ n.primeFactorsList.length := by rw [Finset.prod_pow_eq_pow_sum, hs]

/-- On every fixed bounded x-scale, all sufficiently large rough integers
have at most ceil(2/gamma) prime factors and at most 2^ceil(2/gamma) divisors. -/
theorem marked_rough_factor_and_divisor_count_eventually (T : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ T * x →
      MarkedRoughAbove (x ^ γ) n →
      n.primeFactorsList.length ≤ ⌈2 / γ⌉₊ ∧ n.divisors.card ≤ 2 ^ ⌈2 / γ⌉₊ := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_ge_atTop T] with x hx hTx
  intro n hn hnT hrough
  have hnx : (n : ℝ) ≤ x ^ (2 : ℝ) := by
    simpa only [Real.rpow_two, pow_two] using
      hnT.trans (mul_le_mul_of_nonneg_right hTx (by linarith : 0 ≤ x))
  have hcount := marked_rough_factor_count hn hx hγ hnx hrough
  have hN : n.primeFactorsList.length ≤ ⌈2 / γ⌉₊ := by
    exact_mod_cast hcount.trans (Nat.le_ceil (2 / γ))
  exact ⟨hN, (prime_extraction_divisor_count_le hn).trans
    (Nat.pow_le_pow_right (by norm_num) hN)⟩

end ArtinMatthews
