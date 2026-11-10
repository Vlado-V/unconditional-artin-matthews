module

public import ArtinMatthews.SIntegerAwayQuotient
public import ArtinMatthews.SIntegerFinitePrincipalization
public import ArtinMatthews.SIntegerExteriorIdealEquiv
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

/-! Canonical quotient equivalences for the actually constructed finite
principal S-integer enlargement. No representative coverage or quotient
bijection is supplied as a premise. -/
namespace ArtinMatthews.SIntegerQuotient

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open scoped NumberField BigOperators Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def principalQuotientEquiv (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K))
    (hc : IsCoprime I (Ideal.span {principalizingDenominator S₀})) :
    ((𝓞 K) ⧸ I) ≃ₐ[𝓞 K] (PrincipalIntegerRing S₀) ⧸ I.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
  let : IsLocalization.Away (principalizingDenominator S₀) (PrincipalIntegerRing S₀) :=
    principalIntegerRing_isLocalization S₀
  exact awayQuotientEquiv _ I hc

theorem principalQuotientEquiv_mk (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K))
    (hc : IsCoprime I (Ideal.span {principalizingDenominator S₀})) (x : 𝓞 K) :
    principalQuotientEquiv S₀ I hc (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk (I.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)))
        (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) := rfl

theorem principal_quotient_coverage (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K))
    (hc : IsCoprime I (Ideal.span {principalizingDenominator S₀})) (z : PrincipalIntegerRing S₀) :
    ∃ x : 𝓞 K, z - algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x ∈
      I.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
  let : IsLocalization.Away (principalizingDenominator S₀) (PrincipalIntegerRing S₀) :=
    principalIntegerRing_isLocalization S₀
  exact away_quotient_representative _ I hc z

theorem principal_quotient_card (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K))
    (hc : IsCoprime I (Ideal.span {principalizingDenominator S₀})) :
    Nat.card ((PrincipalIntegerRing S₀) ⧸ I.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) = Ideal.absNorm I := by
  rw [Nat.card_congr (principalQuotientEquiv S₀ I hc).toEquiv.symm,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem principalPrimePower_coprime (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀) (n : ℕ) :
    IsCoprime (P.asIdeal ^ n) (Ideal.span {principalizingDenominator S₀}) := by
  have hd : principalizingDenominator S₀ ∉ P.asIdeal := by
    intro hd
    exact hP ((mem_denominatorSupport _ (principalizingDenominator_ne_zero S₀) P).mpr hd)
  exact (prime_coprime_span_of_not_mem P.asIdeal (P.isPrime.isMaximal P.ne_bot) _ hd).pow_left

def principalPrimePowerQuotientEquiv (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀) (n : ℕ) :
    ((𝓞 K) ⧸ P.asIdeal ^ n) ≃ₐ[𝓞 K]
      (PrincipalIntegerRing S₀) ⧸ (P.asIdeal ^ n).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) :=
  principalQuotientEquiv S₀ _ (principalPrimePower_coprime S₀ P hP n)

theorem principalPrimePowerQuotient_card (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀) (n : ℕ) :
    Nat.card ((PrincipalIntegerRing S₀) ⧸
      (P.asIdeal ^ n).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) = Ideal.absNorm P.asIdeal ^ n := by
  rw [principal_quotient_card S₀ _ (principalPrimePower_coprime S₀ P hP n), map_pow]

theorem generator_power_ideal (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n : ℕ) :
    (P.asIdeal ^ n).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a ^ n} := by
  rw [Ideal.map_pow, ha, Ideal.span_singleton_pow]

def generatorQuotientEquiv (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n : ℕ) :
    ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) ≃+* ((𝓞 K) ⧸ P.asIdeal ^ n) :=
  ((principalPrimePowerQuotientEquiv S₀ P hP n).toRingEquiv.trans
    (Ideal.quotEquivOfEq (generator_power_ideal S₀ P a ha n))).symm

theorem generatorQuotientEquiv_mk (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n : ℕ) (x : 𝓞 K) :
    generatorQuotientEquiv S₀ P hP a ha n
      (Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x)) = Ideal.Quotient.mk _ x := by
  let e := (principalPrimePowerQuotientEquiv S₀ P hP n).toRingEquiv.trans
    (Ideal.quotEquivOfEq (generator_power_ideal S₀ P a ha n))
  have hp : principalPrimePowerQuotientEquiv S₀ P hP n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) :=
    principalQuotientEquiv_mk S₀ _ _ x
  have he : e (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) := by
    rw [RingEquiv.trans_apply]
    erw [hp, Ideal.quotEquivOfEq_mk]
  change e.symm _ = _
  rw [← he, e.symm_apply_apply]

theorem generatorQuotientEquiv_symm_mk (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n : ℕ) (x : 𝓞 K) :
    (generatorQuotientEquiv S₀ P hP a ha n).symm (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap (𝓞 K) (PrincipalIntegerRing S₀) x) := by
  apply (generatorQuotientEquiv S₀ P hP a ha n).injective
  rw [RingEquiv.apply_symm_apply, generatorQuotientEquiv_mk]

theorem generatorQuotient_card (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n : ℕ) :
    Nat.card ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) = Ideal.absNorm P.asIdeal ^ n := by
  rw [Nat.card_congr (generatorQuotientEquiv S₀ P hP a ha n).toEquiv]
  calc
    Nat.card ((𝓞 K) ⧸ P.asIdeal ^ n) = Ideal.absNorm (P.asIdeal ^ n) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = _ := map_pow Ideal.absNorm _ _

end
end ArtinMatthews.SIntegerQuotient
