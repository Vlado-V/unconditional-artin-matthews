module

public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SIntegerPrincipalExterior
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

/-! Unique ideal factorization in the literal exterior-prime coordinates. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]

def sourceExteriorPrimeIdealEmbedding (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    SourceExteriorPrime F S₀ ↪ Ideal (𝓞 F) where
  toFun P := P.val.asIdeal
  inj' := fun _ _ h => Subtype.ext (HeightOneSpectrum.asIdeal_injective h)

theorem sourcePrimeExponentIdeal_embDomain (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e : SourcePrimeExponents F S₀) :
    (e.embDomain (sourceExteriorPrimeIdealEmbedding F S₀)).prod (fun I n => I ^ n) =
      sourcePrimeExponentIdeal F S₀ e :=
  Finsupp.prod_embDomain

theorem sourcePrimeExponentIdeal_factorization (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e : SourcePrimeExponents F S₀) :
    factorization (sourcePrimeExponentIdeal F S₀ e) =
      e.embDomain (sourceExteriorPrimeIdealEmbedding F S₀) := by
  classical
  rw [← sourcePrimeExponentIdeal_embDomain, ← Finsupp.prod_toMultiset]
  unfold factorization
  rw [normalizedFactors_prod_of_prime]
  · exact Finsupp.toMultiset_toFinsupp _
  · intro I hI
    rw [Finsupp.mem_toMultiset, Finsupp.support_embDomain] at hI
    obtain ⟨P, _, rfl⟩ := Finset.mem_map.mp hI
    exact P.val.prime

theorem sourcePrimeExponentIdeal_injective (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    Function.Injective (sourcePrimeExponentIdeal F S₀) := by
  intro e f hef
  have h := congrArg factorization hef
  rw [sourcePrimeExponentIdeal_factorization, sourcePrimeExponentIdeal_factorization] at h
  exact Finsupp.embDomain_injective (sourceExteriorPrimeIdealEmbedding F S₀) h

theorem sourcePrimeExponentIdeal_exterior (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (e : SourcePrimeExponents F S₀) :
    sourcePrimeExponentIdeal F S₀ e ∈
      exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀)) := by
  apply Submonoid.prod_mem
  intro P _
  apply Submonoid.pow_mem
  exact ⟨P.val.ne_bot, by
    simpa only [pow_one] using
      principalPrimePower_coprime (sourceHilbertSeed F S₀) P.val P.property 1⟩

def sourceExteriorIdealExponents (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀))) :
    SourcePrimeExponents F S₀ :=
  Finsupp.comapDomain (sourceExteriorPrimeIdealEmbedding F S₀) (factorization I.val)
    (sourceExteriorPrimeIdealEmbedding F S₀).injective.injOn

theorem sourceExteriorIdeal_factorization_support
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀))) :
    ↑(factorization I.val).support ⊆ Set.range (sourceExteriorPrimeIdealEmbedding F S₀) := by
  classical
  intro J hJ
  have hmem : J ∈ normalizedFactors I.val := by
    simpa only [support_factorization, Finset.mem_coe, Multiset.mem_toFinset] using hJ
  have hprime := prime_of_normalized_factor J hmem
  let P : HeightOneSpectrum (𝓞 F) := ⟨J, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩
  have hP : P ∉ sourceHilbertSet F S₀ := by
    intro hp
    have hi := (exteriorIdeals_mem_iff (sourceHilbertSeed F S₀) I.val).mp I.property
    exact hi.2 P hp (dvd_of_mem_normalizedFactors hmem)
  exact ⟨⟨P, hP⟩, rfl⟩

theorem sourceExteriorIdealExponents_recover
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀))) :
    sourcePrimeExponentIdeal F S₀ (sourceExteriorIdealExponents F S₀ I) = I.val := by
  classical
  rw [← sourcePrimeExponentIdeal_embDomain]
  have he : (sourceExteriorIdealExponents F S₀ I).embDomain
      (sourceExteriorPrimeIdealEmbedding F S₀) = factorization I.val :=
    Finsupp.embDomain_comapDomain (sourceExteriorIdeal_factorization_support F S₀ I)
  rw [he, ← Finsupp.prod_toMultiset]
  unfold factorization
  rw [Multiset.toFinsupp_toMultiset]
  simpa only [normalize_eq] using prod_normalizedFactors_eq I.property.1

def sourcePrimeExponentIdealEquiv (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    SourcePrimeExponents F S₀ ≃
      exteriorIdeals (principalizingDenominator (sourceHilbertSeed F S₀)) where
  toFun e := ⟨sourcePrimeExponentIdeal F S₀ e, sourcePrimeExponentIdeal_exterior F S₀ e⟩
  invFun I := sourceExteriorIdealExponents F S₀ I
  left_inv e := by
    apply sourcePrimeExponentIdeal_injective F S₀
    exact sourceExteriorIdealExponents_recover F S₀ _
  right_inv I := Subtype.ext (sourceExteriorIdealExponents_recover F S₀ I)

end
end ArtinMatthews
