module

public import ArtinMatthews.SourceReflectionSupportedFrequency
public import ArtinMatthews.SourceReflectionSignedExteriorSupport
public import ArtinMatthews.SourceReflectionSignedExteriorNumerator
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

/-! The valuation support is precisely the image of the source's
supported field-frequency carrier. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "a" => sourcePrimeExponentUnit K hζ S₀
local notation "b" => fun f d => a (sourceReflectionActiveExponents K S₀ f + d)
local notation "Πext" => sourceReflectionSignedExteriorProduct K S₀ hζ hS
local notation "Supported" => SourceReflectionSignedExteriorFrequencySupport K S₀ hζ
local notation "Frequency" => fun f d => SourceReflectionSupportedFrequency K S₀ (b f d) d

theorem sourceReflectionSignedExteriorFrequencySupport_iff_range (f : Finset Pr) (d : E)
    (ν : Kˣ) : Supported f d ν ↔ ν ∈ Set.range (fun u : Frequency f d => u.val.val) := by
  constructor
  · intro hν
    obtain ⟨u, rfl, i, hi⟩ :=
      sourceReflectionSignedExteriorFrequencySupport_exists_supportedTerm K S₀ hζ f d ν hν
    refine ⟨⟨u, ?_⟩, rfl⟩
    change (∀ P, sourceReflectionNumeratorExponents K S₀ (b f d) u P % 3 ≤ 1) ∧
      ∀ P ∈ d.support, sourceReflectionNumeratorExponents K S₀ (b f d) u P = 0
    unfold sourceReflectionNumeratorExponents
    rw [← hi]
    exact (sourceReflectionCombineNumerator K S₀ f d i).property
  · rintro ⟨u, rfl⟩
    have he (P : Pr) :
        (sourceReflectionNumeratorExponents K S₀ (b f d) u.val P : ℤ) =
          exteriorPrincipalValuation P.val (u.val.val * (b f d) ^ 2) :=
      sourceReflectionIntegralNumerator_exponents_eq_order K S₀ hζ (b f d) u.val P
    refine ⟨(sourceReflectionFieldUnit_mem_integer_iff K S₀ _).mp u.val.property, ?_, ?_⟩
    · intro P
      change exteriorPrincipalValuation P.val (u.val.val * (b f d) ^ 2) % 3 ≤ 1
      rw [← he]
      exact_mod_cast u.property.1 P
    · intro P hP
      change exteriorPrincipalValuation P.val (u.val.val * (b f d) ^ 2) = 0
      rw [← he]
      exact_mod_cast u.property.2 P hP

theorem sourceReflectionSignedExteriorProduct_eq_zero_off_frequency_range (h d : E) (f : Finset Pr)
    (hd : sourceReflectionIsSquarefree d) (hhd : Disjoint h.support d.support) (hfd : Disjoint f d.support)
    (ν : Kˣ) (hν : ν ∉ Set.range (fun u : Frequency f d => u.val.val)) :
    Πext (h + d) (f ∪ d.support) ν = 0 :=
  sourceReflectionSignedExteriorProduct_eq_zero_of_not_supported K S₀ hζ hS h d f hd hhd hfd ν
    (fun h => hν ((sourceReflectionSignedExteriorFrequencySupport_iff_range K S₀ hζ f d ν).mp h))

end
end ArtinMatthews.SourceEulerAssembly
