module

public import ArtinMatthews.MarkedEstimateSieve
public import ArtinMatthews.MarkedSieveMertens
public import ArtinMatthews.MarkedProgressionLinear
public import ArtinMatthews.MarkedSieveLevel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite positive sieve, connected to the actual summed
progression discrepancy. No bound on that discrepancy is assumed here. -/

namespace ArtinMatthews

open MeasureTheory OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

/-- The fundamental sieve's concrete progression remainders are bounded
by the full available progression discrepancy once its divisor level fits. -/
theorem marked_sieve_remainders_le_discrepancy (H : ℕ → ℝ) (M : ℝ)
    (Φ : ℝ → ℝ) (T x γ c : ℝ) (m : ℕ)
    (hx : 1 ≤ x) (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c) :
    (∑ d ∈ FundamentalBlockEstimate.levelDivisors (Nat.primesLE ⌊x ^ γ⌋₊)
        (⌊x ^ γ⌋₊ ^ (12 * (m + 1))),
      |predecessorProgressionRemainder (Finset.Icc 0 ⌊T * x⌋₊)
        (fun u => Φ ((u : ℝ) / x) * H u)
        (x * (∫ t in Set.Ioc 0 T, Φ t) * M) d|) ≤
      markedProgressionDiscrepancy H M Φ T x ⌊x ^ c⌋₊ := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊x ^ c⌋₊,
        |predecessorProgressionRemainder (Finset.Icc 0 ⌊T * x⌋₊)
          (fun u => Φ ((u : ℝ) / x) * H u)
          (x * (∫ t in Set.Ioc 0 T, Φ t) * M) d| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (marked_sieve_level_subset (Nat.primesLE ⌊x ^ γ⌋₊) x γ c (12 * (m + 1)) hx hlevel)
        (fun _ _ _ => abs_nonneg _)
    _ = _ := by
      unfold predecessorProgressionRemainder markedProgressionDiscrepancy
      apply Finset.sum_congr rfl
      intro d _
      congr 1
      ring

/-- Positive weighted prime predecessors are bounded by the genuine
small-prime Euler product and the actual progression discrepancy.
The finite bridge needs no smoothness or support assumptions on `Φ`. -/
theorem marked_sieve_progression_bridge (H : ℕ → ℝ) (M : ℝ)
    (Φ : ℝ → ℝ) (T x γ c : ℝ) (m : ℕ)
    (hx : 1 ≤ x) (hΦ : ∀ t, 0 ≤ Φ t) (hH : ∀ u, 0 ≤ H u) (hM : 0 ≤ M)
    (hcut : 2 ≤ ⌊x ^ γ⌋₊) (hm : 20000 ≤ m)
    (hlevel : γ * ((12 * (m + 1) : ℕ) : ℝ) ≤ c) :
    (∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter
        (fun u => (u + 1).Prime ∧ ⌊x ^ γ⌋₊ < u + 1), Φ ((u : ℝ) / x) * H u) ≤
      (x * (∫ t in Set.Ioc 0 T, Φ t) * M) * markedSieveEulerProduct (x ^ γ) *
        (1 + Real.exp (-(m : ℝ) / 2)) +
      markedProgressionDiscrepancy H M Φ T x ⌊x ^ c⌋₊ := by
  have h := marked_prime_predecessor_upper_sieve (Finset.Icc 0 ⌊T * x⌋₊)
    (fun u => Φ ((u : ℝ) / x) * H u) (fun u _ => mul_nonneg (hΦ _) (hH u))
    ⌊x ^ γ⌋₊ m (Nat.primesLE ⌊x ^ γ⌋₊) (x * (∫ t in Set.Ioc 0 T, Φ t) * M)
    hcut hm (mul_nonneg (mul_nonneg (le_trans zero_le_one hx) (integral_nonneg hΦ)) hM)
    (fun _ hp => Nat.prime_of_mem_primesLE hp) (fun _ hp => Nat.le_of_mem_primesLE hp)
  exact h.trans (add_le_add le_rfl
    (marked_sieve_remainders_le_discrepancy H M Φ T x γ c m hx hlevel))

end ArtinMatthews
