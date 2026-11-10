module

public import OAI.NumberTheory.PrimePackets.IdealCoefficients
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.Index
public import ArtinMatthews.KummerSplittingGaloisField
public import ArtinMatthews.KummerSplittingFrobenius
public import ArtinMatthews.KummerSplittingInertia
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact prime-ideal norm fibers in the actual varying-prime Kummer field.
The finite set is the same `idealsOverPrime` used by the actual Dedekind
Euler product and prime-power Mellin series. -/

noncomputable section
namespace ArtinMatthews
open scoped NumberField
open OAI.PrimeDegreePackets

/-- The normalized-factor prime fiber is exactly the actual lying-over set. -/
theorem idealsOverPrime_eq_primesOver (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) :
    (↑(idealsOverPrime K p) : Set (Ideal (𝓞 K))) =
      Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa using hp.ne_zero
  ext Q
  rw [Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 K) hp0]
  simp only [Finset.mem_coe, idealsOverPrime, Multiset.mem_toFinset,
    Ideal.map_span, Set.image_singleton, map_natCast]

/-- Every actual prime above p has norm p when q divides the index. -/
theorem primeKummer_absNorm_eq_prime_of_dvd_index
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (ha0 : (a : ZMod p) ≠ 0) (hqi : q ∣ multiplicativeIndex p a)
    (Q : Ideal (𝓞 (primeKummerField q a)))
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (primeKummerField q a))) :
    Ideal.absNorm Q = p := by
  let : Fact p.Prime := ⟨hp⟩
  let : Q.IsPrime := hQ.1
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQ.2
  let : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {(p : ℤ)})
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(primeKummerField q a/ℚ) Q
  let D : IntegralFrobeniusData (primeKummerField q a) p :=
    ⟨Q, inferInstance, hQ.2.over.symm, σ, hσ⟩
  exact D.residue_card_of_frobenius_eq_one (primeKummer_frobenius_eq_one_of_dvd_index D ha0 hqi)

/-- The actual residue degree is one when q divides the index. -/
theorem primeKummer_inertiaDeg_eq_one_of_dvd_index
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (ha0 : (a : ZMod p) ≠ 0) (hqi : q ∣ multiplicativeIndex p a)
    (Q : Ideal (𝓞 (primeKummerField q a)))
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (primeKummerField q a))) :
    Q.inertiaDeg ℤ = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Q.IsPrime := hQ.1
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQ.2
  let : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (Ideal.span {(p : ℤ)})
  have hpow := Ideal.cardQuot_pow_inertiaDeg (Ideal.span {(p : ℤ)}) Q
  have hbase : (Ideal.span {(p : ℤ)}).cardQuot = p := Int.card_ideal_quot _
  have hnorm : Q.cardQuot = p := primeKummer_absNorm_eq_prime_of_dvd_index hp ha0 hqi Q hQ
  rw [hbase, hnorm] at hpow
  exact (pow_right_inj₀ hp.pos (ne_of_gt hp.one_lt)).mp (by simpa using hpow)

/-- The genuine complete split fiber has cardinal equal to the field degree,
with no analytic density or splitting hypothesis. -/
theorem primeKummer_primesOver_card_eq_finrank_of_dvd_index
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (ha0 : (a : ZMod p) ≠ 0)
    (hqi : q ∣ multiplicativeIndex p a) :
    Nat.card (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (primeKummerField q a))) =
      Module.finrank ℚ (primeKummerField q a) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨D⟩ := exists_integralFrobeniusData (primeKummerField q a) hp
  let : D.primeIdeal.IsMaximal := D.maximal
  let : D.primeIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨D.under_eq.symm⟩
  have haP : ¬ (p : ℤ) ∣ a := fun h => ha0 ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr h)
  have hqQ : (q : 𝓞 (primeKummerField q a)) ∉ D.primeIdeal := by
    simpa only [Int.cast_natCast] using D.int_not_mem hqp
  have haQ := D.int_not_mem haP
  have hI := primeKummer_inertia_eq_bot D.primeIdeal hqQ haQ
  have hf := primeKummer_inertiaDeg_eq_one_of_dvd_index hp ha0 hqi D.primeIdeal
    ⟨inferInstance, inferInstance⟩
  have hcount := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
    (G := Gal(primeKummerField q a/ℚ)) (Ideal.span {(p : ℤ)}) D.primeIdeal
  rw [hI, Nat.card_unique, hf, mul_one, mul_one, IsGalois.card_aut_eq_finrank] at hcount
  exact hcount

/-- The exact norm-p prime-ideal fiber used by the actual Dedekind series. -/
theorem primeKummer_normFiber_card_of_dvd_index
    {p q : ℕ} {a : ℤ} [NeZero q] [NeZero a] (hp : p.Prime)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (ha0 : (a : ZMod p) ≠ 0)
    (hqi : q ∣ multiplicativeIndex p a) :
    ((idealsOverPrime (primeKummerField q a) p).filter (fun Q => Ideal.absNorm Q = p)).card =
      Module.finrank ℚ (primeKummerField q a) := by
  classical
  have hfilter : (idealsOverPrime (primeKummerField q a) p).filter
      (fun Q => Ideal.absNorm Q = p) = idealsOverPrime (primeKummerField q a) p := by
    apply Finset.filter_eq_self.mpr
    intro Q hQ
    apply primeKummer_absNorm_eq_prime_of_dvd_index hp ha0 hqi Q
    rw [← idealsOverPrime_eq_primesOver (primeKummerField q a) hp]
    exact hQ
  rw [hfilter]
  have hcount := primeKummer_primesOver_card_eq_finrank_of_dvd_index hp hqp ha0 hqi
  rw [← idealsOverPrime_eq_primesOver (primeKummerField q a) hp] at hcount
  change (↑(idealsOverPrime (primeKummerField q a) p) : Set (Ideal (𝓞 (primeKummerField q a)))).ncard = _ at hcount
  simpa only [Set.ncard_coe_finset] using hcount

/-- For the large prime exponents of Section 10, each index-divisibility
prime contributes exactly q(q−1) prime ideals of norm p. -/
theorem primeKummer_normFiber_card_large_prime
    {a : ℤ} (ha : a ≠ 0) (ha1 : a ≠ 1) (ham1 : a ≠ -1)
    {p q : ℕ} [NeZero q] [NeZero a] (hp : p.Prime) (hq : q.Prime) (haq : a.natAbs ≤ q)
    (hqp : ¬ (p : ℤ) ∣ (q : ℤ)) (ha0 : (a : ZMod p) ≠ 0)
    (hqi : q ∣ multiplicativeIndex p a) :
    ((idealsOverPrime (primeKummerField q a) p).filter (fun Q => Ideal.absNorm Q = p)).card =
      q * (q - 1) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero a := ⟨ha⟩
  rw [primeKummer_normFiber_card_of_dvd_index hp hqp ha0 hqi,
    finrank_primeKummerField_of_large_prime ha ha1 ham1 hq haq]

end ArtinMatthews
