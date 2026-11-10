module

public import ArtinMatthews.SIntegerFinitePrincipalization
public import ArtinMatthews.SIntegerPrincipalExterior
public import ArtinMatthews.SIntegerPrincipalQuotient
public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual generators of exterior primes in the constructed S-integer
PID have the required prime valuations. These valuations are derived
from ideal extension, not supplied as generator-normalization data. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem principalInteger_power_mem_iff_valuation
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (n : ℕ) (x : PrincipalIntegerRing S₀) :
    x ∈ (P.asIdeal ^ n).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) ↔
      P.valuation K (x : K) ≤ WithZero.exp (-(n : ℤ)) := by
  let : IsLocalization.Away (principalizingDenominator S₀) (PrincipalIntegerRing S₀) :=
    principalIntegerRing_isLocalization S₀
  have hd : principalizingDenominator S₀ ∉ P.asIdeal := by
    intro hd
    exact hP ((mem_denominatorSupport _ (principalizingDenominator_ne_zero S₀) P).mpr hd)
  obtain ⟨m, r, he⟩ := exists_mul_pow_integer (principalizingDenominator S₀)
    (principalizingDenominator_ne_zero S₀) (principalizingSet S₀)
    (fun Q => mem_denominatorSupport _ _ Q) x
  have hvd : P.valuation K (algebraMap (𝓞 K) K (principalizingDenominator S₀)) = 1 :=
    P.valuation_eq_one_iff_notMem.mpr hd
  have hv : P.valuation K (x : K) = P.intValuation r := by
    have h := congrArg (P.valuation K) he
    simpa only [map_mul, map_pow, hvd, one_pow, mul_one, P.valuation_of_algebraMap] using h
  have heA : x * algebraMap (𝓞 K) (PrincipalIntegerRing S₀) (principalizingDenominator S₀) ^ m =
      algebraMap (𝓞 K) (PrincipalIntegerRing S₀) r := by
    apply Subtype.ext
    exact he
  have hu : IsUnit (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)
      (principalizingDenominator S₀) ^ m) :=
    (IsLocalization.Away.algebraMap_isUnit (principalizingDenominator S₀)).pow m
  have hr : algebraMap (𝓞 K) (PrincipalIntegerRing S₀) r ∈
      (P.asIdeal ^ n).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) ↔ r ∈ P.asIdeal ^ n := by
    change r ∈ ((P.asIdeal ^ n).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))).under (𝓞 K) ↔ _
    rw [away_under_map_of_coprime (principalizingDenominator S₀) _
      (principalPrimePower_coprime S₀ P hP n)]
  rw [← Ideal.mul_unit_mem_iff_mem _ hu, heA, hr, hv]
  exact (P.intValuation_le_pow_iff_mem r n).symm

theorem exterior_generator_ne_zero
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    a ≠ 0 := by
  intro h
  have he : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = ⊥ := by
    simpa only [h, Ideal.span_singleton_zero] using ha
  exact P.ne_bot ((Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 K) (PrincipalIntegerRing S₀))).mp he)

theorem exterior_generator_nonunit
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    ¬ IsUnit a := by
  let : IsLocalization.Away (principalizingDenominator S₀) (PrincipalIntegerRing S₀) :=
    principalIntegerRing_isLocalization S₀
  intro hu
  have ht : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = ⊤ :=
    ha.trans (Ideal.span_singleton_eq_top.mpr hu)
  have hc := away_under_map_of_coprime (A := PrincipalIntegerRing S₀)
    (principalizingDenominator S₀) P.asIdeal
    (by simpa only [pow_one] using principalPrimePower_coprime S₀ P hP 1)
  rw [ht, Ideal.under_top] at hc
  exact P.isPrime.ne_top hc.symm

theorem exterior_generator_not_mem_square
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    a ∉ (P.asIdeal ^ 2).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
  intro hm
  rw [generator_power_ideal S₀ P a ha 2, Ideal.mem_span_singleton] at hm
  obtain ⟨b, hb⟩ := hm
  have ha0 := exterior_generator_ne_zero S₀ P a ha
  have hab : a * b = 1 := by
    apply mul_left_cancel₀ ha0
    calc
      a * (a * b) = a ^ 2 * b := by ring
      _ = a := hb.symm
      _ = a * 1 := (mul_one a).symm
  exact exterior_generator_nonunit S₀ P hP a ha
    (IsUnit.of_mul_eq_one b hab)

theorem exterior_generator_valuation
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    P.valuation K (a : K) = WithZero.exp (-1 : ℤ) := by
  have haK : (a : K) ≠ 0 := by
    intro he
    exact exterior_generator_ne_zero S₀ P a ha (Subtype.ext he)
  have hv0 : P.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr haK
  have hmem : a ∈ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
    rw [ha]
    exact Ideal.mem_span_singleton_self a
  have hle : P.valuation K (a : K) ≤ WithZero.exp (-1 : ℤ) := by
    simpa only [pow_one, Nat.cast_one] using
      (principalInteger_power_mem_iff_valuation S₀ P hP 1 a).mp (by simpa only [pow_one] using hmem)
  have hnle : ¬ P.valuation K (a : K) ≤ WithZero.exp (-2 : ℤ) := by
    simpa only [Nat.cast_ofNat] using
      ((principalInteger_power_mem_iff_valuation S₀ P hP 2 a).not).mp
        (exterior_generator_not_mem_square S₀ P hP a ha)
  have hl := (WithZero.log_le_log hv0 WithZero.exp_ne_zero).mpr hle
  have hnl := (WithZero.log_le_log hv0 WithZero.exp_ne_zero).not.mpr hnle
  simp only [WithZero.log_exp] at hl hnl
  have he : WithZero.log (P.valuation K (a : K)) = -1 := by omega
  rw [← WithZero.exp_log hv0, he]

theorem exterior_generator_other_valuation
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (Q : HeightOneSpectrum (𝓞 K)) (hQS : Q ∉ principalizingSet S₀) (hQP : Q ≠ P) :
    Q.valuation K (a : K) = 1 := by
  have hn : ¬ P.asIdeal ≤ Q.asIdeal := by
    intro hle
    exact hQP (HeightOneSpectrum.asIdeal_injective
      ((P.isPrime.isMaximal P.ne_bot).eq_of_le Q.isPrime.ne_top hle).symm)
  obtain ⟨r, hrP, hrQ⟩ := IsConcreteLE.not_le_iff_exists.mp hn
  have hm : algebraMap (𝓞 K) (PrincipalIntegerRing S₀) r ∈ Ideal.span {a} := by
    rw [← ha]
    exact Ideal.mem_map_of_mem _ hrP
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hm
  have hbK : (r : K) = (a : K) * (b : K) := congrArg (fun x : PrincipalIntegerRing S₀ => (x : K)) hb
  have hmK : (1 : WithZero (Multiplicative ℤ)) = Q.valuation K (a : K) * Q.valuation K (b : K) := by
    have hqr : Q.valuation K (r : K) = 1 := Q.valuation_eq_one_iff_notMem.mpr hrQ
    calc
      1 = Q.valuation K (r : K) := hqr.symm
      _ = _ := by rw [hbK, map_mul]
  apply le_antisymm (a.property Q hQS)
  calc
    1 = Q.valuation K (a : K) * Q.valuation K (b : K) := hmK
    _ ≤ Q.valuation K (a : K) * 1 := mul_le_mul_right (b.property Q hQS) _
    _ = Q.valuation K (a : K) := mul_one _

theorem exists_exterior_prime_generator
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) :
    ∃ a : PrincipalIntegerRing S₀,
      P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a} := by
  let I : exteriorIdeals (principalizingDenominator S₀) :=
    ⟨P.asIdeal, P.ne_bot, by simpa only [pow_one] using principalPrimePower_coprime S₀ P hP 1⟩
  obtain ⟨u, a, hua, ha⟩ := exists_exterior_field_generator S₀ I
  exact ⟨a, ha⟩

def exteriorPrimeGenerator
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) : PrincipalIntegerRing S₀ :=
  (exists_exterior_prime_generator S₀ P hP).choose

theorem exteriorPrimeGenerator_ideal
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) :
    P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) =
      Ideal.span {exteriorPrimeGenerator S₀ P hP} :=
  (exists_exterior_prime_generator S₀ P hP).choose_spec

theorem exteriorPrimeGenerator_ne_zero
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) : exteriorPrimeGenerator S₀ P hP ≠ 0 :=
  exterior_generator_ne_zero S₀ P _ (exteriorPrimeGenerator_ideal S₀ P hP)

theorem exteriorPrimeGenerator_valuation
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) :
    P.valuation K (exteriorPrimeGenerator S₀ P hP : K) = WithZero.exp (-1 : ℤ) :=
  exterior_generator_valuation S₀ P hP _ (exteriorPrimeGenerator_ideal S₀ P hP)

theorem exteriorPrimeGenerator_other_valuation
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (Q : HeightOneSpectrum (𝓞 K))
    (hQS : Q ∉ principalizingSet S₀) (hQP : Q ≠ P) :
    Q.valuation K (exteriorPrimeGenerator S₀ P hP : K) = 1 :=
  exterior_generator_other_valuation S₀ P _ (exteriorPrimeGenerator_ideal S₀ P hP) Q hQS hQP

end
end ArtinMatthews.SIntegerQuotient
