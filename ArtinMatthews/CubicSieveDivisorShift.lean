module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! The finite prime Euler factor for the divisor weight in Section 7.1.
The two shifts retain their exact divisibility and quotient conditions. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def cubicSieveDivisorShift (a : ℕ) (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  if a ∣ n then F (n / a) else 0

theorem cubicSieve_divisorShift_mul (a b : ℕ) (ha : 0 < a) (F : ℕ → ℝ) (n : ℕ) :
    cubicSieveDivisorShift a (cubicSieveDivisorShift b F) n =
      cubicSieveDivisorShift (a * b) F n := by
  by_cases h : a ∣ n
  · have hb : b ∣ n / a ↔ a * b ∣ n := by
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        calc
          n = a * (n / a) := (Nat.mul_div_cancel' h).symm
          _ = (a * b) * k := by rw [hk, mul_assoc]
      · rintro ⟨k, rfl⟩
        rw [mul_assoc, Nat.mul_div_cancel_left _ ha]
        exact dvd_mul_right _ _
    by_cases h' : b ∣ n / a
    · simp only [cubicSieveDivisorShift, ite_eq_left h, ite_eq_left h',
        ite_eq_left (hb.mp h'), Nat.div_div_eq_div_mul]
    · simp only [cubicSieveDivisorShift, ite_eq_left h, ite_eq_right h',
        ite_eq_right (fun h'' => h' (hb.mpr h''))]
  · have hab : ¬a * b ∣ n := fun hh => h ((dvd_mul_right a b).trans hh)
    simp only [cubicSieveDivisorShift, ite_eq_right h, ite_eq_right hab]

theorem cubicSieve_divisorShift_gate (r a : ℕ) (hc : r.Coprime a) (F : ℕ → ℝ) (n : ℕ) :
    (if r ∣ n then cubicSieveDivisorShift a F n else 0) =
      cubicSieveDivisorShift a (fun t => if r ∣ t then F t else 0) n := by
  by_cases h : a ∣ n
  · have hgate : r ∣ n ↔ r ∣ n / a := by
      constructor
      · intro hr
        apply hc.dvd_of_dvd_mul_left
        rwa [Nat.mul_div_cancel' h]
      · intro hr
        simpa only [Nat.mul_div_cancel' h] using dvd_mul_of_dvd_right hr a
    simp only [cubicSieveDivisorShift, ite_eq_left h, hgate]
  · simp only [cubicSieveDivisorShift, ite_eq_right h, ite_self]

theorem cubicSieve_divisorShift_sum {ι : Type*} (S : Finset ι) (a : ℕ) (ha : 0 < a)
    (c : ι → ℝ) (d : ι → ℕ) (F : ℕ → ℝ) (n : ℕ) :
    cubicSieveDivisorShift a (fun t => ∑ i ∈ S, c i * cubicSieveDivisorShift (d i) F t) n =
      ∑ i ∈ S, c i * cubicSieveDivisorShift (a * d i) F n := by
  simp_rw [← cubicSieve_divisorShift_mul a _ ha F n]
  by_cases h : a ∣ n
  · simp only [cubicSieveDivisorShift, ite_eq_left h]
  · simp only [cubicSieveDivisorShift, ite_eq_right h, mul_zero, Finset.sum_const_zero]

theorem cubicSieve_divisorCount_prime_shift {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (if p ∣ n then (n.divisors.card : ℝ) else 0) =
      2 * cubicSieveDivisorShift p (fun t => (t.divisors.card : ℝ)) n -
        cubicSieveDivisorShift (p * p) (fun t => (t.divisors.card : ℝ)) n := by
  by_cases hn : n = 0
  · subst n
    simp [cubicSieveDivisorShift]
  obtain ⟨k, u, hpu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hc := hp.coprime_iff_not_dvd.mpr hpu
  have hcount (j : ℕ) : ((p ^ j * u).divisors.card : ℝ) =
      ((j : ℝ) + 1) * (u.divisors.card : ℝ) := by
    rw [(hc.pow_left j).card_divisors_mul, Nat.divisors_prime_pow hp,
      Finset.card_map, Finset.card_range]
    push_cast
    rfl
  cases k with
  | zero =>
    have hpp : ¬p * p ∣ u := fun h => hpu ((dvd_mul_right p p).trans h)
    simp only [pow_zero, one_mul, ite_eq_right hpu, cubicSieveDivisorShift,
      ite_eq_right hpp, mul_zero, sub_zero]
  | succ k =>
    cases k with
    | zero =>
      have hu : p ^ (0 + 1) * u = p * u := by rw [zero_add, pow_one]
      rw [hu]
      have hpp : ¬p * p ∣ p * u := fun h => hpu (Nat.dvd_of_mul_dvd_mul_left hp.pos h)
      have h := hcount 1
      simp only [pow_one, Nat.cast_one] at h
      simp only [dvd_mul_right, ite_true, cubicSieveDivisorShift,
        ite_eq_right hpp, Nat.mul_div_cancel_left _ hp.pos, sub_zero]
      rw [h]
      ring
    | succ k =>
      change (if p ∣ p ^ (k + 2) * u then (((p ^ (k + 2) * u).divisors.card : ℝ)) else 0) = _
      have h₁ : p ^ (k + 2) * u = p * (p ^ (k + 1) * u) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ']
        ring
      have h₂ : p ^ (k + 2) * u = (p * p) * (p ^ k * u) := by
        rw [pow_add, pow_two]
        ring
      have hp₁ : p ∣ p ^ (k + 2) * u := h₁ ▸ dvd_mul_right _ _
      have hp₂ : p * p ∣ p ^ (k + 2) * u := h₂ ▸ dvd_mul_right _ _
      have hq₁ : (p ^ (k + 2) * u) / p = p ^ (k + 1) * u := by
        rw [h₁, Nat.mul_div_cancel_left _ hp.pos]
      have hq₂ : (p ^ (k + 2) * u) / (p * p) = p ^ k * u := by
        rw [h₂, Nat.mul_div_cancel_left _ (Nat.mul_pos hp.pos hp.pos)]
      simp only [cubicSieveDivisorShift, ite_eq_left hp₁, ite_eq_left hp₂, hq₁, hq₂,
        hcount]
      push_cast
      ring

end ArtinMatthews
