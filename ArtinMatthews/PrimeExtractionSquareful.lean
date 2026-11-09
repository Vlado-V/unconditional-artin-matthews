module

public import ArtinMatthews.MarkedTypeIICollisionDecay
public import ArtinMatthews.MarkedTypeIICoefficients
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Cast.Order.Field


set_option backward.privateInPublic true
@[expose] public section

/-! The actual squareful exceptional set in prime extraction. Exact counts
of multiples and the reciprocal-square tail give a power saving. -/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def primeSquarefulUpTo (N : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter fun n =>
    n ≠ 0 ∧ ∃ p : ℕ, p.Prime ∧ z < (p : ℝ) ∧ p ^ 2 ∣ n

noncomputable def roughNonsquarefreeUpTo (N : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter fun n =>
    n ≠ 0 ∧ MarkedRoughAbove z n ∧ ¬Squarefree n

/-- Count actual integers divisible by the square of a prime above z. -/
theorem primeSquarefulUpTo_card_le (N : ℕ) {z : ℝ} (hz : 4 ≤ z) :
    ((primeSquarefulUpTo N z).card : ℝ) ≤ 4 * (N : ℝ) / z := by
  classical
  let P : Finset ℕ := (Finset.range (N + 1)).filter fun (p : ℕ) => p.Prime ∧ z < (p : ℝ)
  let Q (p : ℕ) := (Finset.range (N + 1)).filter fun n => n ≠ 0 ∧ p ^ 2 ∣ n
  have hsub : primeSquarefulUpTo N z ⊆ P.biUnion Q := by
    intro n hn
    obtain ⟨hnN, hn0, p, hp, hzp, hpn⟩ := Finset.mem_filter.mp hn
    have hpd : p ∣ n := (dvd_mul_right p p).trans (by simpa only [pow_two] using hpn)
    have hple : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd
    apply Finset.mem_biUnion.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨?_, hp, hzp⟩, Finset.mem_filter.mpr ⟨hnN, hn0, hpn⟩⟩
    exact Finset.mem_range.mpr (lt_of_le_of_lt hple (Finset.mem_range.mp hnN))
  have hcard : (primeSquarefulUpTo N z).card ≤ ∑ p ∈ P, (Q p).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    ((primeSquarefulUpTo N z).card : ℝ) ≤ ∑ p ∈ P, ((Q p).card : ℝ) := by exact_mod_cast hcard
    _ = ∑ p ∈ P, ((N / p ^ 2 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [Q, Nat.card_multiples']
    _ ≤ ∑ p ∈ P, (N : ℝ) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      exact_mod_cast (Nat.cast_div_le (m := N) (n := p ^ 2) (α := ℝ))
    _ = (N : ℝ) * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ (N : ℝ) * (4 / z) := mul_le_mul_of_nonneg_left
      (marked_reciprocal_square_tail_le P hz (fun _ hp => (Finset.mem_filter.mp hp).2.2.le))
      (Nat.cast_nonneg N)
    _ = _ := by ring

theorem roughNonsquarefreeUpTo_subset (N : ℕ) (z : ℝ) :
    roughNonsquarefreeUpTo N z ⊆ primeSquarefulUpTo N z := by
  classical
  intro n hn
  obtain ⟨hnN, hn0, hnrough, hnsq⟩ := Finset.mem_filter.mp hn
  have hp : ∃ p, p.Prime ∧ p * p ∣ n := by
    by_contra h
    apply hnsq
    exact Nat.squarefree_iff_prime_squarefree.mpr (fun p hp hpn => h ⟨p, hp, hpn⟩)
  obtain ⟨p, hp, hpn⟩ := hp
  apply Finset.mem_filter.mpr
  refine ⟨hnN, hn0, p, hp, ?_, by simpa only [pow_two] using hpn⟩
  exact hnrough p hp ((dvd_mul_right p p).trans hpn)

/-- Every non-squarefree rough integer belongs to the square-divisibility
exceptional set, so the count has the same uniform bound. -/
theorem roughNonsquarefreeUpTo_card_le (N : ℕ) {z : ℝ} (hz : 4 ≤ z) :
    ((roughNonsquarefreeUpTo N z).card : ℝ) ≤ 4 * (N : ℝ) / z := by
  calc
    _ ≤ ((primeSquarefulUpTo N z).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (roughNonsquarefreeUpTo_subset N z)
    _ ≤ _ := primeSquarefulUpTo_card_le N hz

/-- Arbitrary bounded complex coefficients can be removed on this actual
exceptional set, without a cancellation or distribution premise. -/
theorem roughNonsquarefreeUpTo_weighted_le (N : ℕ) {z C : ℝ} (hz : 4 ≤ z)
    (hC : 0 ≤ C) (a : ℕ → ℂ)
    (ha : ∀ n ∈ roughNonsquarefreeUpTo N z, ‖a n‖ ≤ C) :
    ‖∑ n ∈ roughNonsquarefreeUpTo N z, a n‖ ≤ C * (4 * (N : ℝ) / z) := by
  calc
    _ ≤ ∑ n ∈ roughNonsquarefreeUpTo N z, ‖a n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ roughNonsquarefreeUpTo N z, C := Finset.sum_le_sum ha
    _ = C * ((roughNonsquarefreeUpTo N z).card : ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (roughNonsquarefreeUpTo_card_le N hz) hC

end ArtinMatthews
