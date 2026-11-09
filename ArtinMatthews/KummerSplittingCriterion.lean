module

public import ArtinMatthews.KummerSplittingPrimeIdeals


set_option backward.privateInPublic true
@[expose] public section

/-! Both directions of the concrete Kummer splitting/index criterion,
including exact zero and full-degree norm fibers. -/

noncomputable section
namespace ArtinMatthews
open scoped NumberField
open OAI.PrimeDegreePackets

section GeneralFrobenius
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
attribute [local instance] Ideal.Quotient.field

/-- At a degree-one residue field any arithmetic Frobenius lies in inertia. -/
theorem IntegralFrobeniusData.frobenius_mem_inertia_of_residue_card
    {p : ℕ} (D : IntegralFrobeniusData K p)
    (hcard : Nat.card (𝓞 K ⧸ D.primeIdeal) = p) :
    D.frobenius ∈ D.primeIdeal.inertia Gal(K/ℚ) := by
  let : D.primeIdeal.IsMaximal := D.maximal
  let : Fintype (𝓞 K ⧸ D.primeIdeal) := Fintype.ofFinite _
  intro x
  apply (Ideal.Quotient.eq_zero_iff_mem (I := D.primeIdeal)).mp
  have hpow : (Ideal.Quotient.mk D.primeIdeal x) ^ p = Ideal.Quotient.mk D.primeIdeal x := by
    simpa only [← Nat.card_eq_fintype_card, hcard] using
      FiniteField.pow_card (Ideal.Quotient.mk D.primeIdeal x)
  rw [map_sub, D.residue_frobenius, hpow, sub_self]
end GeneralFrobenius

/-- A single actual norm-p prime ideal forces divisibility of the index. -/
theorem dvd_index_of_primeKummer_absNorm_eq_prime
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (ha0 : (a : ZMod p) ≠ 0)
    (Q : Ideal (𝓞 (primeKummerField q a)))
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (primeKummerField q a)))
    (hN : Ideal.absNorm Q = p) : q ∣ multiplicativeIndex p a := by
  let : Fact p.Prime := ⟨hp⟩
  let : Q.IsPrime := hQ.1
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQ.2
  let : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {(p : ℤ)})
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(primeKummerField q a/ℚ) Q
  let D : IntegralFrobeniusData (primeKummerField q a) p :=
    ⟨Q, inferInstance, hQ.2.over.symm, σ, hσ⟩
  have haP : ¬ (p : ℤ) ∣ a := fun h => ha0 ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr h)
  have hqQ : (q : 𝓞 (primeKummerField q a)) ∉ D.primeIdeal := by
    simpa only [Int.cast_natCast] using D.int_not_mem hqp
  have hI := primeKummer_inertia_eq_bot D.primeIdeal hqQ (D.int_not_mem haP)
  have hmem := D.frobenius_mem_inertia_of_residue_card hN
  rw [hI, Subgroup.mem_bot] at hmem
  exact (primeKummer_frobenius_eq_one_iff_dvd_index D hqp ha0).mp hmem

/-- Every prime ideal in the actual fiber has norm p precisely at the
index-divisibility primes. -/
theorem primeKummer_absNorm_eq_prime_iff_dvd_index
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (ha0 : (a : ZMod p) ≠ 0)
    (Q : Ideal (𝓞 (primeKummerField q a)))
    (hQ : Q ∈ idealsOverPrime (primeKummerField q a) p) :
    Ideal.absNorm Q = p ↔ q ∣ multiplicativeIndex p a := by
  have hQ' : Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (primeKummerField q a)) := by
    rw [← idealsOverPrime_eq_primesOver (primeKummerField q a) hp]
    exact hQ
  exact ⟨dvd_index_of_primeKummer_absNorm_eq_prime hp hqp ha0 Q hQ',
    fun hqi => primeKummer_absNorm_eq_prime_of_dvd_index hp ha0 hqi Q hQ'⟩

/-- Exact actual norm-p fiber cardinal: full field degree or zero. -/
theorem primeKummer_normFiber_card
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (ha0 : (a : ZMod p) ≠ 0) :
    ((idealsOverPrime (primeKummerField q a) p).filter (fun Q => Ideal.absNorm Q = p)).card =
      if q ∣ multiplicativeIndex p a then Module.finrank ℚ (primeKummerField q a) else 0 := by
  classical
  by_cases hi : q ∣ multiplicativeIndex p a
  · rw [ite_eq_left hi]
    exact primeKummer_normFiber_card_of_dvd_index hp hqp ha0 hi
  · rw [ite_eq_right hi, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro Q hQ hN
    exact hi ((primeKummer_absNorm_eq_prime_iff_dvd_index hp hqp ha0 Q hQ).mp hN)

/-- Exact q(q−1)-or-zero fiber in the large-prime range of Section 10. -/
theorem primeKummer_normFiber_card_large_prime_ite
    {a : ℤ} (ha : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {p q : ℕ} [NeZero q] [NeZero a] (hp : p.Prime) (hq : q.Prime)
    (haq : a.natAbs ≤ q) (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (ha0 : (a : ZMod p) ≠ 0) :
    ((idealsOverPrime (primeKummerField q a) p).filter (fun Q => Ideal.absNorm Q = p)).card =
      if q ∣ multiplicativeIndex p a then q * (q - 1) else 0 := by
  rw [primeKummer_normFiber_card hp hqp ha0,
    finrank_primeKummerField_of_large_prime ha ha1 ham1 hq haq]

end ArtinMatthews
