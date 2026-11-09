module

public import ArtinMatthews.LargeFactor
public import ArtinMatthews.ExceptionalAsymptotic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Finite subtraction in the final sieve

This module formalizes the finite counting step in Section 10.3. A candidate
prime has `p - 1 = k * Q` with `Q` prime and `k` within the exceptional product's
cutoff. Outside the small-index set, the arithmetic dichotomy in `LargeFactor`
puts it in the actual simultaneous primitive-root set or in the prime divisors
of the exceptional product.

The candidate weighted lower bound and the small-index counting estimate remain
explicit hypotheses. No analytic estimate producing those hypotheses, and no
unconditional positive-density assertion, is claimed here.
-/

namespace ArtinMatthews

/-- Finite weighted subtraction. The three covering sets need not be disjoint.
Only the upper bound on each weight is needed for this counting inequality. -/
theorem weighted_sum_sub_losses_le_card {α : Type*} [DecidableEq α]
    {P G B E : Finset α} {w : α → ℝ}
    (hw : ∀ p ∈ P, w p ≤ 1)
    (hcover : ∀ p ∈ P, p ∈ G ∨ p ∈ B ∨ p ∈ E) :
    (∑ p ∈ P, w p) - (B.card : ℝ) - (E.card : ℝ) ≤ (G.card : ℝ) := by
  have hsum : (∑ p ∈ P, w p) ≤ (P.card : ℝ) := by
    calc
      (∑ p ∈ P, w p) ≤ ∑ _p ∈ P, (1 : ℝ) := Finset.sum_le_sum hw
      _ = (P.card : ℝ) := by simp
  have hsubset : P ⊆ (G ∪ B) ∪ E := by
    intro p hp
    rcases hcover p hp with hG | hB | hE
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hG)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hB)
    · exact Finset.mem_union_right _ hE
  have hcard : P.card ≤ G.card + B.card + E.card :=
    (Finset.card_le_card hsubset).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hcard' : (P.card : ℝ) ≤ (G.card : ℝ) + (B.card : ℝ) + (E.card : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- Candidates removed because a prime at most `m` divides one of their
multiplicative indices. -/
noncomputable def smallIndexCandidates (S : Finset ℤ) (P : Finset ℕ) (m : ℕ) :
    Finset ℕ := by
  classical
  exact P.filter fun p =>
    ∃ a ∈ S, ∃ q : ℕ, q.Prime ∧ q ≤ m ∧ q ∣ multiplicativeIndex p a

theorem mem_smallIndexCandidates {S : Finset ℤ} {P : Finset ℕ} {m p : ℕ} :
    p ∈ smallIndexCandidates S P m ↔
      p ∈ P ∧ ∃ a ∈ S, ∃ q : ℕ, q.Prime ∧ q ≤ m ∧ q ∣ multiplicativeIndex p a := by
  classical
  simp only [smallIndexCandidates, Finset.mem_filter]

/-- The arithmetic cover underlying the subtraction: actual simultaneous
primitive-root primes, small index primes, and divisors of the short product. -/
theorem candidate_mem_simultaneous_or_smallIndex_or_exceptional
    {S : Finset ℤ} (hS : AdmissibleBases S) {P : Finset ℕ} {m : ℕ} {x : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, x < (p : ℝ))
    (hnonzero : ∀ p ∈ P, ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (hfactor : ∀ p ∈ P, ∃ k Q : ℕ, Q.Prime ∧ p - 1 = k * Q ∧ k ≤ m)
    {p : ℕ} (hp : p ∈ P) :
    p ∈ SimultaneousPrimitivePrimes S ∨ p ∈ smallIndexCandidates S P m ∨
      p ∈ primeFactorsAbove (exceptionalProduct S m) x := by
  classical
  by_cases hbad : p ∈ smallIndexCandidates S P m
  · exact Or.inr (Or.inl hbad)
  obtain ⟨k, Q, hQ, hpk, hkm⟩ := hfactor p hp
  have hsmall : ∀ a ∈ S, ∀ q : ℕ,
      q.Prime → q ≤ k → ¬ q ∣ multiplicativeIndex p a := by
    intro a ha q hq hqk hdiv
    exact hbad (mem_smallIndexCandidates.mpr
      ⟨hp, a, ha, q, hq, hqk.trans hkm, hdiv⟩)
  rcases simultaneous_or_dvd_exceptionalProduct (hprime p hp) hQ
      (hnonzero p hp) hpk hkm hsmall with hsim | hdiv
  · exact Or.inl hsim
  · exact Or.inr (Or.inr (mem_primeFactorsAbove.mpr
      ⟨hprime p hp, hdiv, (exceptionalProduct_pos hS m).ne', hlarge p hp⟩))

/-- Any finite set of actual simultaneous primes in `(x, 2*x]` is counted by
the dyadic counting function, including its real cutoff convention. -/
theorem card_le_dyadicCount {S : Finset ℤ} {P : Finset ℕ} {x : ℝ}
    (hP : ∀ p ∈ P, x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
      p ∈ SimultaneousPrimitivePrimes S) :
    P.card ≤ dyadicCount S x := by
  classical
  unfold dyadicCount
  apply Finset.card_le_card
  intro p hp
  refine Finset.mem_filter.mpr ⟨?_, hP p hp⟩
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  apply Nat.le_floor
  exact (hP p hp).2.1.trans
    (mul_le_mul_of_nonneg_left (le_max_left x 0) (by norm_num))

/-- The finite subtraction in Section 10.3, with the two losses left as exact
cardinalities. The surviving primes satisfy the original simultaneous predicate. -/
theorem weighted_candidates_sub_losses_le_dyadicCount
    {S : Finset ℤ} (hS : AdmissibleBases S) {P : Finset ℕ}
    {w : ℕ → ℝ} {m : ℕ} {x : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hinterval : ∀ p ∈ P, x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x)
    (hnonzero : ∀ p ∈ P, ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (hfactor : ∀ p ∈ P, ∃ k Q : ℕ, Q.Prime ∧ p - 1 = k * Q ∧ k ≤ m)
    (hweights : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1) :
    (∑ p ∈ P, w p) - ((smallIndexCandidates S P m).card : ℝ) -
      ((primeFactorsAbove (exceptionalProduct S m) x).card : ℝ) ≤
        (dyadicCount S x : ℝ) := by
  classical
  let G := P.filter fun p => p ∈ SimultaneousPrimitivePrimes S
  have hcover : ∀ p ∈ P, p ∈ G ∨ p ∈ smallIndexCandidates S P m ∨
      p ∈ primeFactorsAbove (exceptionalProduct S m) x := by
    intro p hp
    rcases candidate_mem_simultaneous_or_smallIndex_or_exceptional hS hprime
        (fun p hp => (hinterval p hp).1) hnonzero hfactor hp with hsim | hrest
    · exact Or.inl (Finset.mem_filter.mpr ⟨hp, hsim⟩)
    · exact Or.inr hrest
  have hG : G.card ≤ dyadicCount S x := by
    apply card_le_dyadicCount
    intro p hp
    obtain ⟨hpP, hsim⟩ := Finset.mem_filter.mp hp
    exact ⟨(hinterval p hpP).1, (hinterval p hpP).2, hsim⟩
  exact (weighted_sum_sub_losses_le_card (fun p hp => (hweights p hp).2) hcover).trans
    (by exact_mod_cast hG)

/-- A lower bound `A` on the weighted candidate count and upper bounds `B, C`
on the actual two exceptional counts give the numerical bound `A - B - C`.
The analytic estimates supplying `A` and `B` are assumptions of this theorem. -/
theorem dyadicCount_ge_of_weighted_candidates
    {S : Finset ℤ} (hS : AdmissibleBases S) {P : Finset ℕ}
    {w : ℕ → ℝ} {m : ℕ} {x A B C : ℝ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hinterval : ∀ p ∈ P, x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x)
    (hnonzero : ∀ p ∈ P, ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (hfactor : ∀ p ∈ P, ∃ k Q : ℕ, Q.Prime ∧ p - 1 = k * Q ∧ k ≤ m)
    (hweights : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1)
    (hA : A ≤ ∑ p ∈ P, w p)
    (hB : ((smallIndexCandidates S P m).card : ℝ) ≤ B)
    (hC : ((primeFactorsAbove (exceptionalProduct S m) x).card : ℝ) ≤ C) :
    A - B - C ≤ (dyadicCount S x : ℝ) := by
  have h := weighted_candidates_sub_losses_le_dyadicCount hS hprime hinterval
    hnonzero hfactor hweights
  linarith

/-- The same numerical subtraction with the exceptional-product loss discharged
by its proved logarithmic bound. Only the candidate and small-index estimates
remain as input bounds. -/
theorem dyadicCount_ge_of_weighted_candidates_product_bound
    {S : Finset ℤ} (hS : AdmissibleBases S) {P : Finset ℕ}
    {w : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m) {x A B : ℝ} (hx : 1 < x)
    (hprime : ∀ p ∈ P, p.Prime)
    (hinterval : ∀ p ∈ P, x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x)
    (hnonzero : ∀ p ∈ P, ∀ a ∈ S, (a : ZMod p) ≠ 0)
    (hfactor : ∀ p ∈ P, ∃ k Q : ℕ, Q.Prime ∧ p - 1 = k * Q ∧ k ≤ m)
    (hweights : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1)
    (hA : A ≤ ∑ p ∈ P, w p)
    (hB : ((smallIndexCandidates S P m).card : ℝ) ≤ B) :
    A - B - productGrowthConstant S * (m : ℝ) ^ 2 / Real.log x ≤
      (dyadicCount S x : ℝ) :=
  dyadicCount_ge_of_weighted_candidates hS hprime hinterval hnonzero hfactor hweights
    hA hB (card_exceptional_primeFactorsAbove_le hS hm hx)

end ArtinMatthews
