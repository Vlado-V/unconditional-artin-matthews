module

public import ArtinMatthews.KummerSplittingCriterion
public import Mathlib.NumberTheory.RamificationInertia.Unramified


set_option backward.privateInPublic true
@[expose] public section

/-! Precise ramification exclusions for the actual varying-q Kummer field. -/

namespace ArtinMatthews
open scoped NumberField

/-- Every actual prime above a rational prime away from a and q is unramified. -/
theorem primeKummer_unramifiedAt_of_not_dvd
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (hap : ¬ (p : ℤ) ∣ a)
    (Q : Ideal (𝓞 (primeKummerField q a))) [Q.IsPrime]
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (primeKummerField q a))) :
    Algebra.IsUnramifiedAt ℤ Q := by
  let : Fact p.Prime := ⟨hp⟩
  let : Q.IsPrime := hQ.1
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQ.2
  let : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {(p : ℤ)})
  have hnot (b : ℤ) (hb : ¬ (p : ℤ) ∣ b) : (b : 𝓞 (primeKummerField q a)) ∉ Q := by
    intro hmem
    have hh : b ∈ Q.under ℤ := hmem
    rw [← hQ.2.over, Ideal.mem_span_singleton] at hh
    exact hb hh
  have hqQ : (q : 𝓞 (primeKummerField q a)) ∉ Q := by
    simpa only [Int.cast_natCast] using hnot q hqp
  exact Ideal.ramificationIdx_eq_one_iff.mp
    (primeKummer_ramificationIdx_eq_one Q hqQ (hnot a hap))

/-- Ramification in the actual Kummer field is excluded by the single
rational condition p ∤ a q. -/
theorem primeKummer_unramifiedAt_of_not_dvd_mul
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (hpaq : ¬ (p : ℤ) ∣ a * (q : ℤ))
    (Q : Ideal (𝓞 (primeKummerField q a))) [Q.IsPrime]
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (primeKummerField q a))) :
    Algebra.IsUnramifiedAt ℤ Q := by
  apply primeKummer_unramifiedAt_of_not_dvd (q := q) (a := a) hp
  · exact fun h => hpaq (dvd_mul_of_dvd_right h a)
  · exact fun h => hpaq (dvd_mul_of_dvd_left h (q : ℤ))
  · exact hQ

/-- The classical complete-splitting condition, expressed using the actual
ramification indices and residue degrees of every prime above p, is exactly
the multiplicative-index condition. -/
theorem primeKummer_completeSplitting_iff_dvd_index
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (ha0 : (a : ZMod p) ≠ 0) :
    (∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (primeKummerField q a)),
      Q.ramificationIdx ℤ = 1 ∧ Q.inertiaDeg ℤ = 1) ↔
      q ∣ multiplicativeIndex p a := by
  let : Fact p.Prime := ⟨hp⟩
  have hap : ¬ (p : ℤ) ∣ a := fun h => ha0 ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr h)
  constructor
  · intro hsplit
    obtain ⟨D⟩ := exists_integralFrobeniusData (primeKummerField q a) hp
    let : D.primeIdeal.IsMaximal := D.maximal
    let : D.primeIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨D.under_eq.symm⟩
    have hQ : D.primeIdeal ∈
        Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (primeKummerField q a)) :=
      ⟨inferInstance, inferInstance⟩
    have hf := (hsplit D.primeIdeal hQ).2
    have hpow := Ideal.cardQuot_pow_inertiaDeg (Ideal.span {(p : ℤ)}) D.primeIdeal
    have hbase : (Ideal.span {(p : ℤ)}).cardQuot = p := Int.card_ideal_quot _
    rw [hbase, hf, pow_one] at hpow
    exact dvd_index_of_primeKummer_absNorm_eq_prime hp hqp ha0 D.primeIdeal hQ hpow.symm
  · intro hi Q hQ
    let : Q.IsPrime := hQ.1
    let : Algebra.IsUnramifiedAt ℤ Q := primeKummer_unramifiedAt_of_not_dvd hp hqp hap Q hQ
    exact ⟨Ideal.ramificationIdx_eq_one_of_isUnramifiedAt,
      primeKummer_inertiaDeg_eq_one_of_dvd_index hp ha0 hi Q hQ⟩

end ArtinMatthews
