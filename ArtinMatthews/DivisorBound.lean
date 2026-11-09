module

public import ArtinMatthews.Definitions
public import Mathlib.Data.Nat.Factorization.Basic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Counting large prime divisors

A finite set of distinct prime divisors of a positive integer has product at
most that integer. Taking logarithms bounds the number of those primes above
a real threshold. This is the elementary product-exclusion estimate.
-/

namespace ArtinMatthews

/-- The product of any finite set of prime divisors of a nonzero integer divides
that integer. Distinctness is supplied by the finset. -/
theorem prod_primes_dvd_of_dvd {P : Finset ℕ} {N : ℕ} (hN : N ≠ 0)
    (hprime : ∀ p ∈ P, p.Prime) (hdvd : ∀ p ∈ P, p ∣ N) :
    (∏ p ∈ P, p) ∣ N := by
  have hsubset : P ⊆ N.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdvd p hp, hN⟩
  exact (Finset.prod_dvd_prod_of_subset P N.primeFactors (fun p => p) hsubset).trans
    (Nat.prod_primeFactors_dvd N)

/-- Logarithmic bound for a finite set of prime divisors exceeding `x`. -/
theorem card_mul_log_le_log_of_primes_dvd {P : Finset ℕ} {N : ℕ} {x : ℝ}
    (hN : 0 < N) (hx : 1 < x) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, x < (p : ℝ)) (hdvd : ∀ p ∈ P, p ∣ N) :
    (P.card : ℝ) * Real.log x ≤ Real.log (N : ℝ) := by
  have hprodpos : 0 < ∏ p ∈ P, p :=
    Finset.prod_pos (fun p hp => (hprime p hp).pos)
  have hprodle : (∏ p ∈ P, p) ≤ N :=
    Nat.le_of_dvd hN (prod_primes_dvd_of_dvd hN.ne' hprime hdvd)
  calc
    (P.card : ℝ) * Real.log x = ∑ p ∈ P, Real.log x := by simp
    _ ≤ ∑ p ∈ P, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log (by linarith) (hlarge p hp).le
    _ = Real.log (∏ p ∈ P, (p : ℝ)) := by
      symm
      apply Real.log_prod
      intro p hp
      exact_mod_cast (hprime p hp).ne_zero
    _ = Real.log ((∏ p ∈ P, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
    _ ≤ Real.log (N : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hprodpos
      · exact_mod_cast hprodle

/-- Dividing the logarithmic product bound by the positive threshold logarithm. -/
theorem card_le_log_div_log_of_primes_dvd {P : Finset ℕ} {N : ℕ} {x : ℝ}
    (hN : 0 < N) (hx : 1 < x) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, x < (p : ℝ)) (hdvd : ∀ p ∈ P, p ∣ N) :
    (P.card : ℝ) ≤ Real.log (N : ℝ) / Real.log x := by
  exact (le_div_iff₀ (Real.log_pos hx)).mpr
    (card_mul_log_le_log_of_primes_dvd hN hx hprime hlarge hdvd)

/-- The distinct prime divisors of `N` exceeding the real cutoff `x`. -/
noncomputable def primeFactorsAbove (N : ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact N.primeFactors.filter fun p => x < (p : ℝ)

theorem mem_primeFactorsAbove {N p : ℕ} {x : ℝ} :
    p ∈ primeFactorsAbove N x ↔ p.Prime ∧ p ∣ N ∧ N ≠ 0 ∧ x < (p : ℝ) := by
  classical
  simp only [primeFactorsAbove, Finset.mem_filter, Nat.mem_primeFactors]
  tauto

/-- A bound for all distinct prime divisors above the cutoff. -/
theorem card_primeFactorsAbove_mul_log_le_log {N : ℕ} {x : ℝ}
    (hN : 0 < N) (hx : 1 < x) :
    ((primeFactorsAbove N x).card : ℝ) * Real.log x ≤ Real.log (N : ℝ) := by
  apply card_mul_log_le_log_of_primes_dvd hN hx
  · intro p hp
    exact (mem_primeFactorsAbove.mp hp).1
  · intro p hp
    exact (mem_primeFactorsAbove.mp hp).2.2.2
  · intro p hp
    exact (mem_primeFactorsAbove.mp hp).2.1

theorem card_primeFactorsAbove_le_log_div_log {N : ℕ} {x : ℝ}
    (hN : 0 < N) (hx : 1 < x) :
    ((primeFactorsAbove N x).card : ℝ) ≤ Real.log (N : ℝ) / Real.log x := by
  exact (le_div_iff₀ (Real.log_pos hx)).mpr
    (card_primeFactorsAbove_mul_log_le_log hN hx)

end ArtinMatthews
