module

public import ArtinMatthews.PrimeExtractionTupleRecursion


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite hyperbola reindexing of the ordered-prime convolution.
The predecessor core may be an arbitrary function of the whole product. -/

namespace ArtinMatthews

open scoped BigOperators

theorem prime_extraction_sum_divisors_reindex (N : ℕ) (w : ℕ → ℂ) (G : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc 0 N, w n * ∑ p ∈ n.divisors, G p (n / p)) =
      ∑ mn ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun mn => mn.1 * mn.2 ≤ N),
        w (mn.1 * mn.2) * G mn.1 mn.2 := by
  classical
  trans ∑ n ∈ Finset.Ioc 0 N,
    ∑ mn ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun mn => mn.1 * mn.2 = n),
      w (mn.1 * mn.2) * G mn.1 mn.2
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum, ← Nat.sum_divisorsAntidiagonal (fun p v => w n * G p v),
      Nat.divisorsAntidiagonal_eq_prod_filter_of_le (Finset.mem_Ioc.mp hn).1.ne'
        (Finset.mem_Ioc.mp hn).2]
    apply Finset.sum_congr rfl
    intro mn hmn
    rw [(Finset.mem_filter.mp hmn).2]
  · simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro mn hmn
    have hm : 0 < mn.1 := (Finset.mem_Ioc.mp (Finset.mem_product.mp hmn).1).1
    have hn : 0 < mn.2 := (Finset.mem_Ioc.mp (Finset.mem_product.mp hmn).2).1
    simp_all

noncomputable def roughPrimeFirstCoefficient (a : ℕ → ℂ) (z : ℝ) (p : ℕ) : ℂ := by
  classical
  exact if p.Prime ∧ z < (p : ℝ) then a p else 0

theorem roughPrimeTupleCoefficient_succ_divisors (a : ℕ → ℂ) (j n : ℕ) (z : ℝ) :
    roughPrimeTupleCoefficient a (j + 1) n z =
      ∑ p ∈ n.divisors, roughPrimeFirstCoefficient a z p * roughPrimeTupleCoefficient a j (n / p) z := by
  classical
  rw [roughPrimeTupleCoefficient_succ]
  simp only [roughPrimeDivisors, Finset.sum_filter, roughPrimeFirstCoefficient, ite_mul, zero_mul]

/-- The exact Type-II-shaped sum, with first coefficient supported on rough
primes and the genuine finite remaining-prime coefficient beta_j. -/
theorem roughPrimeTupleCoefficient_bilinear_expansion (a : ℕ → ℂ) (j N : ℕ)
    (z : ℝ) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc 0 N, w n * roughPrimeTupleCoefficient a (j + 1) n z) =
      ∑ mn ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun mn => mn.1 * mn.2 ≤ N),
        w (mn.1 * mn.2) * roughPrimeFirstCoefficient a z mn.1 *
          roughPrimeTupleCoefficient a j mn.2 z := by
  simp_rw [roughPrimeTupleCoefficient_succ_divisors]
  rw [prime_extraction_sum_divisors_reindex N w
    (fun p v => roughPrimeFirstCoefficient a z p * roughPrimeTupleCoefficient a j v z)]
  apply Finset.sum_congr rfl
  intro mn _
  ring

end ArtinMatthews
