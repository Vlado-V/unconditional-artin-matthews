module

public import ArtinMatthews.PrimeExtractionOrderedFactors


set_option backward.privateInPublic true
@[expose] public section

/-! Isolating the first prime in the actual ordered factorization set. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def roughPrimeDivisors (n : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact n.divisors.filter fun p => p.Prime ∧ z < (p : ℝ)

theorem roughOrderedPrimeFactorizations_nonzero {j n : ℕ} {z : ℝ} {l : List ℕ}
    (hl : l ∈ roughOrderedPrimeFactorizations j n z) : n ≠ 0 := by
  intro hn
  subst n
  rw [roughOrderedPrimeFactorizations, ite_eq_left (rfl : (0 : ℕ) = 0)] at hl
  exact Finset.notMem_empty _ hl

theorem roughOrderedPrimeFactorizations_cons (j n p : ℕ) (z : ℝ) (l : List ℕ) :
    p :: l ∈ roughOrderedPrimeFactorizations (j + 1) n z ↔
      p ∈ roughPrimeDivisors n z ∧ l ∈ roughOrderedPrimeFactorizations j (n / p) z := by
  classical
  constructor
  · intro h
    have hn := roughOrderedPrimeFactorizations_nonzero h
    obtain ⟨hlen, hprod, hprimes⟩ := (mem_roughOrderedPrimeFactorizations _ _ _ _).mp h
    have hp := hprimes p List.mem_cons_self
    have hpd : p ∣ n := hprod ▸ List.dvd_prod List.mem_cons_self
    refine ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hpd, hn⟩, hp⟩, ?_⟩
    apply (mem_roughOrderedPrimeFactorizations _ _ _ _).mpr
    refine ⟨by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen, ?_,
      fun q hq => hprimes q (List.mem_cons_of_mem p hq)⟩
    have hprod' : p * l.prod = n := hprod
    rw [← hprod', Nat.mul_div_right _ hp.1.pos]
  · rintro ⟨hp, hl⟩
    obtain ⟨hpd, hprime, hpz⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlen, hprod, hprimes⟩ := (mem_roughOrderedPrimeFactorizations _ _ _ _).mp hl
    apply (mem_roughOrderedPrimeFactorizations _ _ _ _).mpr
    refine ⟨by simp only [List.length_cons, hlen], ?_, ?_⟩
    · rw [List.prod_cons, hprod, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hpd)]
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨hprime, hpz⟩
      · exact hprimes r hr

theorem roughOrderedPrimeFactorizations_succ (j n : ℕ) (z : ℝ) :
    roughOrderedPrimeFactorizations (j + 1) n z =
      (roughPrimeDivisors n z).biUnion (fun p =>
        (roughOrderedPrimeFactorizations j (n / p) z).image (List.cons p)) := by
  classical
  ext l
  cases l with
  | nil =>
    simp only [mem_roughOrderedPrimeFactorizations, List.length_nil, Finset.mem_biUnion,
      Finset.mem_image]
    simp
  | cons p l =>
    rw [roughOrderedPrimeFactorizations_cons]
    simp only [Finset.mem_biUnion, Finset.mem_image, List.cons.injEq]
    aesop

noncomputable def roughPrimeTupleCoefficient (a : ℕ → ℂ) (j n : ℕ) (z : ℝ) : ℂ :=
  ∑ l ∈ roughOrderedPrimeFactorizations j n z, (l.map a).prod

/-- Exact divisor convolution: the first prime is the first bilinear
variable, and the remaining ordered tuple supplies beta_j. -/
theorem roughPrimeTupleCoefficient_succ (a : ℕ → ℂ) (j n : ℕ) (z : ℝ) :
    roughPrimeTupleCoefficient a (j + 1) n z =
      ∑ p ∈ roughPrimeDivisors n z, a p * roughPrimeTupleCoefficient a j (n / p) z := by
  classical
  unfold roughPrimeTupleCoefficient
  rw [roughOrderedPrimeFactorizations_succ, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_image]
    · simp only [List.map_cons, List.prod_cons, Finset.mul_sum]
    · intro l _ r _ h
      exact (List.cons.inj h).2
  · intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro l hlp hlq
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hlp
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hlq
    exact hpq (List.cons.inj (hr.trans hs.symm)).1

end ArtinMatthews
