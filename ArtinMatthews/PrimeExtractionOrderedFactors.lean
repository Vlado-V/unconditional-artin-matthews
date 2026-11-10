module

public import ArtinMatthews.MarkedTypeIICoefficients
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Actual ordered prime factorizations, with their precise factorial mass.
Repeated primes are retained; only squarefree integers attain the factorial
cardinality used to count each composite exactly once. -/

namespace ArtinMatthews

open scoped BigOperators

def orderedPrimeFactorizations (n : ℕ) : Finset (List ℕ) :=
  n.primeFactorsList.permutations.toFinset

theorem mem_orderedPrimeFactorizations {n : ℕ} (hn : n ≠ 0) (l : List ℕ) :
    l ∈ orderedPrimeFactorizations n ↔ l.prod = n ∧ ∀ p ∈ l, p.Prime := by
  simp only [orderedPrimeFactorizations, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro hl
    exact ⟨hl.prod_eq.trans (Nat.prod_primeFactorsList hn),
      fun p hp => Nat.prime_of_mem_primeFactorsList (hl.mem_iff.mp hp)⟩
  · rintro ⟨hprod, hprime⟩
    exact Nat.primeFactorsList_unique hprod hprime

theorem orderedPrimeFactorizations_length {n : ℕ} {l : List ℕ}
    (hl : l ∈ orderedPrimeFactorizations n) : l.length = n.primeFactorsList.length :=
  (List.mem_permutations.mp (List.mem_toFinset.mp hl)).length_eq

theorem orderedPrimeFactorizations_card_le (n : ℕ) :
    (orderedPrimeFactorizations n).card ≤ n.primeFactorsList.length.factorial := by
  exact (List.toFinset_card_le (l := n.primeFactorsList.permutations)).trans
    (List.length_permutations _).le

theorem orderedPrimeFactorizations_card {n : ℕ} (hn : Squarefree n) :
    (orderedPrimeFactorizations n).card = n.primeFactorsList.length.factorial := by
  rw [orderedPrimeFactorizations, List.toFinset_card_of_nodup
    (List.nodup_permutations _ ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn)),
    List.length_permutations]

theorem orderedPrimeFactorizations_nodup {n : ℕ} (hn : Squarefree n)
    {l : List ℕ} (hl : l ∈ orderedPrimeFactorizations n) : l.Nodup :=
  (List.mem_permutations.mp (List.mem_toFinset.mp hl)).nodup_iff.mpr
    ((Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn)

/-- The factorial weight is exactly the reciprocal of the number of
ordered factorizations of each squarefree integer. -/
theorem squarefree_ordered_factorization_average {n : ℕ} (hn : Squarefree n) (b : ℂ) :
    (∑ _l ∈ orderedPrimeFactorizations n, b) / n.primeFactorsList.length.factorial = b := by
  rw [Finset.sum_const, nsmul_eq_mul, orderedPrimeFactorizations_card hn]
  have hfac : (n.primeFactorsList.length.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

noncomputable def roughOrderedPrimeFactorizations (j n : ℕ) (z : ℝ) : Finset (List ℕ) := by
  classical
  exact if n = 0 then ∅ else
    (orderedPrimeFactorizations n).filter fun l => l.length = j ∧ ∀ p ∈ l, z < (p : ℝ)

theorem mem_roughOrderedPrimeFactorizations (j n : ℕ) (z : ℝ) (l : List ℕ) :
    l ∈ roughOrderedPrimeFactorizations j n z ↔
      l.length = j ∧ l.prod = n ∧ ∀ p ∈ l, p.Prime ∧ z < (p : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hnot : ¬(l.length = j ∧ l.prod = 0 ∧ ∀ p ∈ l, p.Prime ∧ z < (p : ℝ)) := by
      rintro ⟨_, hp, hprime⟩
      exact (hprime 0 (List.prod_eq_zero_iff.mp hp)).1.ne_zero rfl
    rw [roughOrderedPrimeFactorizations, ite_eq_left (rfl : (0 : ℕ) = 0)]
    exact iff_of_false (Finset.notMem_empty l) hnot
  · simp only [roughOrderedPrimeFactorizations, ite_eq_right hn, Finset.mem_filter,
      mem_orderedPrimeFactorizations hn]
    aesop

theorem roughOrderedPrimeFactorizations_card_le (j n : ℕ) (z : ℝ) :
    (roughOrderedPrimeFactorizations j n z).card ≤ j.factorial := by
  classical
  by_cases hne : (roughOrderedPrimeFactorizations j n z).Nonempty
  · obtain ⟨l, hl⟩ := hne
    obtain ⟨hlen, hprod, hprime⟩ := (mem_roughOrderedPrimeFactorizations j n z l).mp hl
    have heq : n.primeFactorsList.length = j :=
      (Nat.primeFactorsList_unique hprod (fun p hp => (hprime p hp).1)).length_eq.symm.trans hlen
    have hsub : roughOrderedPrimeFactorizations j n z ⊆ orderedPrimeFactorizations n := by
      intro l hl
      unfold roughOrderedPrimeFactorizations at hl
      split_ifs at hl with hn
      · simp at hl
      · exact (Finset.mem_filter.mp hl).1
    exact (Finset.card_le_card hsub).trans (by simpa only [heq] using orderedPrimeFactorizations_card_le n)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- On a rough squarefree integer with exactly j factors, the tuple set is
the complete set of ordered prime factorizations. -/
theorem roughOrderedPrimeFactorizations_eq {j n : ℕ} (hn : n ≠ 0) {z : ℝ}
    (hrough : MarkedRoughAbove z n) (hj : n.primeFactorsList.length = j) :
    roughOrderedPrimeFactorizations j n z = orderedPrimeFactorizations n := by
  classical
  ext l
  rw [mem_roughOrderedPrimeFactorizations, mem_orderedPrimeFactorizations hn]
  constructor
  · rintro ⟨_, hp, hprime⟩
    exact ⟨hp, fun p hpl => (hprime p hpl).1⟩
  · rintro ⟨hp, hprime⟩
    have hperm := Nat.primeFactorsList_unique hp hprime
    refine ⟨hperm.length_eq.trans hj, hp, fun p hpl => ⟨hprime p hpl, ?_⟩⟩
    exact hrough p (hprime p hpl) (hp ▸ List.dvd_prod hpl)

end ArtinMatthews
