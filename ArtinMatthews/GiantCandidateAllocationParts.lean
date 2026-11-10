module

public import ArtinMatthews.GiantCandidatePrimeStrip
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Arithmetic of the actual active prime part and its complement.
The factors are split before imposing any squarefreeness restriction. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantCandidatePrimePart_eq_one_of_coprime (P : Finset ℕ) {m : ℕ}
    (hm : 0 < m) (hc : (∏ p ∈ P, p).Coprime m) :
    giantCandidatePrimePart P m = 1 := by
  by_contra h
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h
  obtain ⟨hpm, hpP⟩ := (prime_dvd_commonPrimePart_iff hm.ne' hp _).mp hd
  exact (hp.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hpP hc)) hpm

theorem giantCandidatePrimePart_eq_self_of_dvd_part (P : Finset ℕ) {m n : ℕ}
    (hn : 0 < n) (hm : m ∣ giantCandidatePrimePart P n) :
    giantCandidatePrimePart P m = m := by
  let D := ∏ p ∈ P, p
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    exact commonPrimePart_ne_zero hn.ne' D (zero_dvd_iff.mp hm)
  apply Nat.eq_of_factorization_eq (commonPrimePart_ne_zero hm0 D) hm0
  rw [factorization_commonPrimePart]
  intro p
  by_cases hp : p ∣ D
  · simp only [Finsupp.filter_apply, ite_eq_left hp]
  · have hs : p ∉ m.factorization.support := by
      rw [Nat.support_factorization]
      intro h
      have hd := (Nat.dvd_of_mem_primeFactors h).trans hm
      exact hp ((prime_dvd_commonPrimePart_iff hn.ne' (Nat.prime_of_mem_primeFactors h) D).mp hd).2
    have hz := Finsupp.notMem_support_iff.mp hs
    rw [Finsupp.filter_apply, ite_eq_right hp, hz]

theorem giantCandidateStrip_dvd (P : Finset ℕ) (m : ℕ) :
    giantCandidateStrip P m ∣ m :=
  ⟨giantCandidatePrimePart P m, by
    rw [mul_comm, giantCandidatePrimePart_mul_strip]⟩

theorem giantCandidatePrimePart_prod {ι : Type*} (P : Finset ℕ) (S : Finset ι)
    (m : ι → ℕ) (hm : ∀ i ∈ S, 0 < m i) :
    giantCandidatePrimePart P (∏ i ∈ S, m i) =
      ∏ i ∈ S, giantCandidatePrimePart P (m i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    exact giantCandidatePrimePart_eq_one_of_coprime P Nat.one_pos (Nat.coprime_one_right _)
  | @insert i S hi ih =>
    rw [prod_insert hi, prod_insert hi]
    have hprod : 0 < ∏ k ∈ S, m k := prod_pos (fun k hk => hm k (mem_insert_of_mem hk))
    have he : giantCandidatePrimePart P (m i * ∏ k ∈ S, m k) =
        giantCandidatePrimePart P (m i) * giantCandidatePrimePart P (∏ k ∈ S, m k) :=
      commonPrimePart_mul (hm i (mem_insert_self i S)).ne' hprod.ne' _
    rw [he, ih (fun k hk => hm k (mem_insert_of_mem hk))]

theorem giantCandidateStrip_prod {ι : Type*} (P : Finset ℕ) (S : Finset ι)
    (m : ι → ℕ) (hm : ∀ i ∈ S, 0 < m i) :
    giantCandidateStrip P (∏ i ∈ S, m i) = ∏ i ∈ S, giantCandidateStrip P (m i) := by
  have hprod : 0 < ∏ i ∈ S, m i := prod_pos hm
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (commonPrimePart_ne_zero hprod.ne' (∏ p ∈ P, p)))
  calc
    _ = ∏ i ∈ S, m i := giantCandidatePrimePart_mul_strip P _
    _ = ∏ i ∈ S, giantCandidatePrimePart P (m i) * giantCandidateStrip P (m i) :=
      prod_congr rfl (fun i _ => (giantCandidatePrimePart_mul_strip P (m i)).symm)
    _ = _ := by rw [prod_mul_distrib, ← giantCandidatePrimePart_prod P S m hm]

theorem giantCandidatePrimePart_primeFactors (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : 0 < n) :
    (giantCandidatePrimePart P n).primeFactors = activeDivisors P n := by
  classical
  let D := ∏ p ∈ P, p
  have hpD (p : ℕ) (hp : p.Prime) : p ∣ D ↔ p ∈ P := by
    constructor
    · intro h
      obtain ⟨q, hq, hd⟩ := (hp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp h
      have he := (Nat.prime_dvd_prime_iff_eq hp (hP q hq)).mp hd
      exact he.symm ▸ hq
    · exact fun h => dvd_prod_of_mem (fun q => q) h
  ext p
  rw [activeDivisors, mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hd, _⟩
    obtain ⟨hnp, hpd⟩ := (prime_dvd_commonPrimePart_iff hn.ne' hp D).mp hd
    exact ⟨(hpD p hp).mp hpd, hnp⟩
  · rintro ⟨hp, hd⟩
    exact ⟨hP p hp, (prime_dvd_commonPrimePart_iff hn.ne' (hP p hp) D).mpr
      ⟨hd, (hpD p (hP p hp)).mpr hp⟩, commonPrimePart_ne_zero hn.ne' D⟩

theorem giantCandidatePrimePart_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : 0 < n) (hnsq : ∀ p ∈ P, ¬ p ^ 2 ∣ n) :
    Squarefree (giantCandidatePrimePart P n) := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  have hpn : p ∣ giantCandidatePrimePart P n := (Nat.dvd_mul_right p p).trans hd
  have hmem : p ∈ (giantCandidatePrimePart P n).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpn, commonPrimePart_ne_zero hn.ne' _⟩
  rw [giantCandidatePrimePart_primeFactors P hP hn] at hmem
  apply hnsq p (mem_filter.mp hmem).1
  rw [pow_two]
  exact hd.trans (commonPrimePart_dvd n _)

end
end ArtinMatthews
