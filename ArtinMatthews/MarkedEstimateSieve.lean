module

public import OAI.NumberTheory.Jacobsthal.Estimates.FundamentalBlockEstimate
public import ArtinMatthews.MarkedEstimateDeweighting


set_option backward.privateInPublic true
@[expose] public section

/-!
# A positive sieve for weighted prime predecessors

This specializes a proved finite fundamental-lemma estimate from the OAI
library to the bad events `p ∣ u + 1`. Its error is the actual sum of
progression remainders; no equidistribution assertion is assumed or hidden.
The divisor level is `V ^ (12 * (m + 1))` and the relative sieve error is
`exp (-m/2)`. These constants differ from the manuscript's block sieve,
but suffice after reducing its positive sieve exponent.
-/

namespace ArtinMatthews

set_option maxHeartbeats 600000

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

/-- The actual discrepancy from density `1/d` for the predecessor weight. -/
noncomputable def predecessorProgressionRemainder (C : Finset ℕ)
    (w : ℕ → ℝ) (X : ℝ) (d : ℕ) : ℝ := by
  classical
  exact (∑ u ∈ C with d ∣ u + 1, w u) - X / (d : ℝ)

/-- The shifted positive sieve's integer remainder is the usual progression
remainder on every squarefree divisor. -/
theorem predecessor_integerRemainder (C : Finset ℕ) (w : ℕ → ℝ)
    (X : ℝ) {d : ℕ} (hd : Squarefree d) :
    FundamentalBlockEstimate.integerRemainder C w (fun p u => p ∣ u + 1)
      X (fun p => 1 / (p : ℝ)) d = predecessorProgressionRemainder C w X d := by
  classical
  have hdprod := Nat.prod_primeFactors_of_squarefree hd
  have hdiv (u : ℕ) : (∀ p ∈ d.primeFactors, p ∣ u + 1) ↔ d ∣ u + 1 := by
    constructor
    · intro h
      rw [← hdprod, Nat.prod_primeFactors_dvd_iff (by omega : u + 1 ≠ 0)]
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, h p hp, by omega⟩
    · intro h p hp
      exact (Nat.dvd_of_mem_primeFactors hp).trans h
  have hprod : (∏ p ∈ d.primeFactors, 1 / (p : ℝ)) = 1 / (d : ℝ) := by
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const_one]
    congr 1
    rw [← Nat.cast_prod, hdprod]
  unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
    BonferroniBlocks.intersectionMass BonferroniBlocks.intersectionValue
    predecessorProgressionRemainder
  simp only [hdiv, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [hprod]
  simp only [div_eq_mul_inv, one_mul]

/-- A completely finite upper sieve for prime predecessors. `X` is an
arbitrary proposed main mass; all errors in that proposal remain explicit. -/
theorem marked_prime_predecessor_upper_sieve (C : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ u ∈ C, 0 ≤ w u) (V m : ℕ) (P : Finset ℕ) (X : ℝ)
    (hV : 2 ≤ V) (hm : 20000 ≤ m) (hX : 0 ≤ X)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ V) :
    (∑ u ∈ C with (u + 1).Prime ∧ V < u + 1, w u) ≤
      X * (∏ p ∈ P, (1 - 1 / (p : ℝ))) * (1 + Real.exp (-(m : ℝ) / 2)) +
        ∑ d ∈ FundamentalBlockEstimate.levelDivisors P (V ^ (12 * (m + 1))),
          |predecessorProgressionRemainder C w X d| := by
  classical
  have hg0 : ∀ p ∈ P, 0 ≤ (1 : ℝ) / p := by intros; positivity
  have hdim : ∀ p ∈ P, (1 : ℝ) / p ≤ 2 / p := by
    intro p hp
    apply div_le_div_of_nonneg_right (by norm_num)
    positivity
  have htwo : 2 ∈ P → (1 : ℝ) / 2 ≤ 1 / 2 := fun _ => le_rfl
  have h := FundamentalBlockEstimate.finite_fundamental_integer_level
    C w hw (fun p u => p ∣ u + 1) V m P X (fun p => 1 / (p : ℝ))
    hV hm hX hprime hsize hg0 hdim htwo
  have hrem : (∑ d ∈ FundamentalBlockEstimate.levelDivisors P (V ^ (12 * (m + 1))),
      |FundamentalBlockEstimate.integerRemainder C w (fun p u => p ∣ u + 1)
        X (fun p => 1 / (p : ℝ)) d|) =
      ∑ d ∈ FundamentalBlockEstimate.levelDivisors P (V ^ (12 * (m + 1))),
        |predecessorProgressionRemainder C w X d| := by
    apply Finset.sum_congr rfl
    intro d hd
    have hpd : d ∣ ∏ p ∈ P, p := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    rw [predecessor_integerRemainder C w X
      ((IntervalBoundingSieve.squarefree_primeSet_product P hprime).squarefree_of_dvd hpd)]
  rw [hrem] at h
  have hsurvive : (∑ u ∈ C with (u + 1).Prime ∧ V < u + 1, w u) ≤
      ∑ u ∈ C, w u * BonferroniBlocks.survives P (fun p => p ∣ u + 1) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro u hu
    unfold BonferroniBlocks.survives
    split_ifs with hp hs hs
    · simp
    · exfalso
      apply hs
      intro p hpP hpu
      have heq := (Nat.prime_dvd_prime_iff_eq (hprime p hpP) hp.1).mp hpu
      have := hsize p hpP
      omega
    · simpa using hw u hu
    · simp
  have hupper := (abs_le.mp h).2
  nlinarith

/-- The positive sieve and Cauchy step combined: a prime deweighting error
is bounded solely by the actual predecessor progression remainders of its
nonnegative squared discrepancy weight. -/
theorem marked_prime_deweighting_by_progressions (C : Finset ℕ)
    (w d : ℕ → ℝ) (a : ℕ → ℂ) {B : ℝ}
    (hw : ∀ u ∈ C, 0 ≤ w u) (hB : 0 ≤ B) (ha : ∀ u ∈ C, ‖a u‖ ≤ B)
    (V m : ℕ) (P : Finset ℕ) (X : ℝ)
    (hV : 2 ≤ V) (hm : 20000 ≤ m) (hX : 0 ≤ X)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ V) :
    ‖∑ u ∈ C with (u + 1).Prime ∧ V < u + 1,
        (w u : ℂ) * a u * (d u : ℂ)‖ ≤
      B * Real.sqrt (∑ u ∈ C with (u + 1).Prime ∧ V < u + 1, w u) *
        Real.sqrt (X * (∏ p ∈ P, (1 - 1 / (p : ℝ))) *
          (1 + Real.exp (-(m : ℝ) / 2)) +
          ∑ r ∈ FundamentalBlockEstimate.levelDivisors P (V ^ (12 * (m + 1))),
            |predecessorProgressionRemainder C (fun u => w u * d u ^ 2) X r|) := by
  classical
  have hsieve := marked_prime_predecessor_upper_sieve C (fun u => w u * d u ^ 2)
    (fun u hu => mul_nonneg (hw u hu) (sq_nonneg _)) V m P X hV hm hX hprime hsize
  apply (marked_deweighting_bound
    (C.filter (fun u => (u + 1).Prime ∧ V < u + 1)) w d a
    (fun u hu => hw u (Finset.mem_filter.mp hu).1) hB
    (fun u hu => ha u (Finset.mem_filter.mp hu).1)).trans
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsieve)
    (mul_nonneg hB (Real.sqrt_nonneg _))

end ArtinMatthews
