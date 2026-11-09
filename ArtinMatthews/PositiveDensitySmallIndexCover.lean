module

public import ArtinMatthews.SieveAssembly
public import Mathlib.NumberTheory.PrimeCounting


set_option backward.privateInPublic true
@[expose] public section

/-! The actual small-index candidates after the fixed congruence
exclusions are the union of the remaining prime-index fibers. -/

noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def giantSieveRemainingIndexPrimes (Y m : ℕ) : Finset ℕ :=
  (Nat.primesLE m).filter fun q => Y < q

theorem mem_giantSieveRemainingIndexPrimes {Y m q : ℕ} :
    q ∈ giantSieveRemainingIndexPrimes Y m ↔ q.Prime ∧ Y < q ∧ q ≤ m := by
  simp only [giantSieveRemainingIndexPrimes, Finset.mem_filter, Nat.mem_primesLE]
  tauto

theorem giantSieveRemainingIndexPrimes_card_le (Y m : ℕ) :
    (giantSieveRemainingIndexPrimes Y m).card ≤ m := by
  have hsub : giantSieveRemainingIndexPrimes Y m ⊆ Finset.Icc 1 m := by
    intro q hq
    obtain ⟨hprime, _, hm⟩ := mem_giantSieveRemainingIndexPrimes.mp hq
    exact Finset.mem_Icc.mpr ⟨hprime.one_lt.le, hm⟩
  exact (Finset.card_le_card hsub).trans (by simp)

def giantSieveIndexFiber (P : Finset ℕ) (a : ℤ) (q : ℕ) : Finset ℕ :=
  P.filter fun p => q ∣ multiplicativeIndex p a

def giantSievePrimeIndexFiber (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℤ) (q : ℕ) :
    Finset Nat.Primes :=
  (giantSieveIndexFiber P a q).attach.map
    (⟨fun p => ⟨p.val, hP _ (Finset.mem_filter.mp p.property).1⟩,
      fun _ _ h => Subtype.ext (congrArg (fun r : Nat.Primes => r.val) h)⟩ :
      ↥(giantSieveIndexFiber P a q) ↪ Nat.Primes)

theorem mem_giantSievePrimeIndexFiber {P : Finset ℕ} {hP : ∀ p ∈ P, p.Prime}
    {a : ℤ} {q : ℕ} {p : Nat.Primes} :
    p ∈ giantSievePrimeIndexFiber P hP a q ↔
      p.val ∈ P ∧ q ∣ multiplicativeIndex p.val a := by
  rw [giantSievePrimeIndexFiber, Finset.mem_map]
  constructor
  · rintro ⟨r, _, hr⟩
    have heq := congrArg (fun r : Nat.Primes => r.val) hr
    exact heq ▸ (Finset.mem_filter.mp r.property)
  · intro hp
    exact ⟨⟨p.val, Finset.mem_filter.mpr hp⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

theorem giantSievePrimeIndexFiber_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : ℤ) (q : ℕ) :
    (giantSievePrimeIndexFiber P hP a q).card = (giantSieveIndexFiber P a q).card := by
  simp only [giantSievePrimeIndexFiber, Finset.card_map, Finset.card_attach]

theorem giantSieve_smallIndex_eq_union (S : Finset ℤ) (P : Finset ℕ) (Y m : ℕ)
    (havoid : ∀ p ∈ P, ∀ a ∈ S, ∀ q, q.Prime → q ≤ Y → ¬ q ∣ multiplicativeIndex p a) :
    smallIndexCandidates S P m =
      S.biUnion (fun a => (giantSieveRemainingIndexPrimes Y m).biUnion (giantSieveIndexFiber P a)) := by
  classical
  ext p
  simp only [mem_smallIndexCandidates, Finset.mem_biUnion, mem_giantSieveRemainingIndexPrimes,
    giantSieveIndexFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hp, a, ha, q, hq, hqm, hdiv⟩
    have hqY : Y < q := lt_of_not_ge fun hqY => havoid p hp a ha q hq hqY hdiv
    exact ⟨a, ha, q, ⟨hq, hqY, hqm⟩, hp, hdiv⟩
  · rintro ⟨a, ha, q, ⟨hq, _, hqm⟩, hp, hdiv⟩
    exact ⟨hp, a, ha, q, hq, hqm, hdiv⟩

theorem giantSieve_smallIndex_card_le_sum (S : Finset ℤ) (P : Finset ℕ) (Y m : ℕ)
    (havoid : ∀ p ∈ P, ∀ a ∈ S, ∀ q, q.Prime → q ≤ Y → ¬ q ∣ multiplicativeIndex p a) :
    ((smallIndexCandidates S P m).card : ℝ) ≤
      ∑ a ∈ S, ∑ q ∈ giantSieveRemainingIndexPrimes Y m, ((giantSieveIndexFiber P a q).card : ℝ) := by
  classical
  rw [giantSieve_smallIndex_eq_union S P Y m havoid]
  calc
    _ ≤ ∑ a ∈ S, (((giantSieveRemainingIndexPrimes Y m).biUnion
        (giantSieveIndexFiber P a)).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun a _ => by exact_mod_cast Finset.card_biUnion_le

end ArtinMatthews
