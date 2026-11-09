module

public import ArtinMatthews.SourceReflectionSignedExteriorNumerator
public import ArtinMatthews.SourceReflectionSupportedFrequency


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
