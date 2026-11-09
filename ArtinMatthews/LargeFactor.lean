module

public import ArtinMatthews.Index


set_option backward.privateInPublic true
@[expose] public section

/-!
# Removing the last large index prime

These are the elementary deductions used after the analytic estimates in
Section 10.  If `p - 1 = k * Q`, every prime divisor of a nontrivial index
either is at most `k` or equals `Q`.  Excluding the former leaves an explicit
divisor of the exceptional product.
-/

namespace ArtinMatthews

/-- Index one is precisely the primitive-root condition for a nonzero residue. -/
theorem multiplicativeIndex_eq_one_iff {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) :
    multiplicativeIndex p a = 1 ↔ IsPrimitiveRootMod p a := by
  constructor
  · intro hi
    exact ⟨ha, by simpa [hi] using orderOf_mul_index hp ha⟩
  · intro h
    unfold multiplicativeIndex
    rw [h.2]
    exact Nat.div_self (by have := hp.two_le; omega)

/-- The multiplicative index divides `p - 1`. -/
theorem multiplicativeIndex_dvd {p : ℕ} (hp : p.Prime) {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) : multiplicativeIndex p a ∣ p - 1 := by
  refine ⟨orderOf (a : ZMod p), ?_⟩
  simpa only [Nat.mul_comm] using (orderOf_mul_index hp ha).symm

/-- A divisor of `k * Q` with no small prime factors is either one or
divisible by the remaining prime `Q`. -/
theorem large_prime_dvd_of_no_small_prime {n k Q : ℕ}
    (hk : 0 < k) (hQ : Q.Prime) (hn : n ∣ k * Q)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ k → ¬ q ∣ n) (hne : n ≠ 1) :
    Q ∣ n := by
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd hne
  rcases hq.dvd_mul.mp (hqn.trans hn) with hqk | hqQ
  · exact False.elim (hsmall q hq (Nat.le_of_dvd hk hqk) hqn)
  · have hqeq : q = Q := (Nat.prime_dvd_prime_iff_eq hq hQ).mp hqQ
    simpa only [hqeq] using hqn

/-- After every index prime at most `k` is excluded, only `Q` can remain. -/
theorem primitive_or_large_prime_dvd_index {p k Q : ℕ} (hp : p.Prime)
    (hQ : Q.Prime) {a : ℤ} (ha : (a : ZMod p) ≠ 0)
    (hpk : p - 1 = k * Q)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ k → ¬ q ∣ multiplicativeIndex p a) :
    IsPrimitiveRootMod p a ∨ Q ∣ multiplicativeIndex p a := by
  by_cases hi : multiplicativeIndex p a = 1
  · exact Or.inl ((multiplicativeIndex_eq_one_iff hp ha).mp hi)
  · right
    have hk : 0 < k := by
      have := hp.two_le
      by_contra h
      have hk0 : k = 0 := by omega
      simp only [hk0, zero_mul] at hpk
      omega
    apply large_prime_dvd_of_no_small_prime hk hQ _ hsmall hi
    rw [← hpk]
    exact multiplicativeIndex_dvd hp ha

/-- Failure to be primitive forces the large prime to divide the index. -/
theorem large_prime_dvd_index_of_not_primitive {p k Q : ℕ} (hp : p.Prime)
    (hQ : Q.Prime) {a : ℤ} (ha : (a : ZMod p) ≠ 0)
    (hpk : p - 1 = k * Q)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ k → ¬ q ∣ multiplicativeIndex p a)
    (hnot : ¬ IsPrimitiveRootMod p a) : Q ∣ multiplicativeIndex p a :=
  (primitive_or_large_prime_dvd_index hp hQ ha hpk hsmall).resolve_left hnot

/-- A nonprimitive base surviving the small-index exclusions satisfies
the short exponent relation `a ^ k = 1` modulo `p`. -/
theorem short_power_eq_one_of_not_primitive {p k Q : ℕ} (hp : p.Prime)
    (hQ : Q.Prime) {a : ℤ} (ha : (a : ZMod p) ≠ 0)
    (hpk : p - 1 = k * Q)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ k → ¬ q ∣ multiplicativeIndex p a)
    (hnot : ¬ IsPrimitiveRootMod p a) : (a : ZMod p) ^ k = 1 :=
  pow_eq_one_of_dvd_index hp hQ.ne_zero ha hpk
    (large_prime_dvd_index_of_not_primitive hp hQ ha hpk hsmall hnot)

/-- Every surviving nonprimitive prime divides the explicit exceptional
product once its cofactor is within the product's exponent range. -/
theorem nonprimitive_dvd_exceptionalProduct {S : Finset ℤ} {a : ℤ}
    (haS : a ∈ S) {p k Q m : ℕ} (hp : p.Prime) (hQ : Q.Prime)
    (ha : (a : ZMod p) ≠ 0) (hpk : p - 1 = k * Q) (hkm : k ≤ m)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ k → ¬ q ∣ multiplicativeIndex p a)
    (hnot : ¬ IsPrimitiveRootMod p a) : p ∣ exceptionalProduct S m := by
  have hk : 1 ≤ k := by
    have := hp.two_le
    by_contra h
    have hk0 : k = 0 := by omega
    simp only [hk0, zero_mul] at hpk
    omega
  apply dvd_exceptionalProduct haS (Finset.mem_Icc.mpr ⟨hk, hkm⟩)
  exact dvd_pow_sub_one_of_dvd_index hp hQ.ne_zero ha hpk
    (large_prime_dvd_index_of_not_primitive hp hQ ha hpk hsmall hnot)

/-- With admissible bases, the same containment is in a finite prime-divisor
set because the exceptional product is nonzero. -/
theorem nonprimitive_mem_exceptionalPrimeFactors {S : Finset ℤ}
    (hS : AdmissibleBases S) {a : ℤ} (haS : a ∈ S)
    {p k Q m : ℕ} (hp : p.Prime) (hQ : Q.Prime)
    (ha : (a : ZMod p) ≠ 0) (hpk : p - 1 = k * Q) (hkm : k ≤ m)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ k → ¬ q ∣ multiplicativeIndex p a)
    (hnot : ¬ IsPrimitiveRootMod p a) :
    p ∈ (exceptionalProduct S m).primeFactors :=
  large_index_exception_mem_primeFactors hS hp hQ.ne_zero haS ha hpk hkm
    (large_prime_dvd_index_of_not_primitive hp hQ ha hpk hsmall hnot)

/-- The set-level dichotomy used in the final sieve: a prime meeting all
small-index exclusions is simultaneous, or divides the exceptional product. -/
theorem simultaneous_or_dvd_exceptionalProduct {S : Finset ℤ}
    {p k Q m : ℕ} (hp : p.Prime) (hQ : Q.Prime)
    (ha : ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (hpk : p - 1 = k * Q) (hkm : k ≤ m)
    (hsmall : ∀ a ∈ S, ∀ q : ℕ,
      q.Prime → q ≤ k → ¬ q ∣ multiplicativeIndex p a) :
    p ∈ SimultaneousPrimitivePrimes S ∨ p ∣ exceptionalProduct S m := by
  by_cases hsim : p ∈ SimultaneousPrimitivePrimes S
  · exact Or.inl hsim
  · right
    by_contra hdiv
    apply hsim
    refine ⟨hp, ?_⟩
    intro a haS
    by_contra hnot
    exact hdiv (nonprimitive_dvd_exceptionalProduct haS hp hQ (ha a haS)
      hpk hkm (hsmall a haS) hnot)

end ArtinMatthews
