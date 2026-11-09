module

public import ArtinMatthews.SourceReflectionTrace
public import ArtinMatthews.SourceReflectionPoissonMoment
public import ArtinMatthews.SourceQuadraticSieveActual


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil
open Filter Asymptotics
open scoped NumberField Classical BigOperators Topology
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
local notation "E" => SourcePrimeExponents F S₀
local notation "Rows" => SourceNonzeroFrequency F S₀
local notation "Classes" => ExteriorUnitSixthClasses (sourceHilbertSet F S₀)

/-- The literal reflected moment with the actual quadratic sieve discharged. -/
theorem exists_sourceReflectionLiteralMoment_le_actual {U : Type} [Fintype U]
    (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A) {K M ε : ℝ}
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ cBound : ℝ, 0 < cBound ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ (X : Finset Rows) (L : ℕ),
      (∀ m ∈ X, (sourcePrimeExponentNorm F S₀
        (sourceElementExponents F S₀ m.val m.property) : ℝ) ≤ K * Z ^ M) →
      (∀ e : E, (X.filter (fun m => sourceElementExponents F S₀ m.val m.property = e)).card ≤ L) →
      ∑ m ∈ X, ‖reflectionCoefficientRow F hζ S₀ hBad η m.val Z‖ ^ 2 ≤
        cBound * (L : ℝ) * Z ^ (2 * M - 1 + ε) :=
  exists_sourceReflectionLiteralMoment_le F S₀ hζ η hBad A hA
    (sourceReflectionQuadraticSieve_actual F S₀ hζ (sourceTraceBadPlaces_subset_of_weil F S₀ hBad))
    hK hM hε

/-- The source Poisson reflected moment requires only its literal expansion. -/
theorem sourcePoissonReflectedSecondMoment_of_expansion_actual {U : Type} [Fintype U]
    (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A) :
    SourcePoissonReflectedSecondMoment F S₀ hζ η hBad :=
  sourcePoissonReflectedSecondMoment_of_expansion F S₀ hζ η hBad A hA
    (sourceReflectionQuadraticSieve_actual F S₀ hζ (sourceTraceBadPlaces_subset_of_weil F S₀ hBad))

/-- The actual physical probe bound following from the literal reflected expansion. -/
theorem sourcePoissonPhysicalProbe_bound_of_expansion_actual {U : Type} [Fintype U]
    (v : InfinitePlace F) (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A) :
    sourcePoissonPhysicalProbeAtScales F S₀ hζ η v hBad =O[atTop]
      (fun Z : ℝ => Z ^ (933 / 2000 + 1 / 100000 : ℝ)) :=
  sourcePoissonPhysicalProbe_bound_of_reflected F S₀ hζ η v hBad
    (sourcePoissonReflectedSecondMoment_of_expansion_actual F S₀ hζ η hBad A hA)

/-- The source-infinity exponent following from the literal reflected expansion. -/
theorem sourcePoissonAngularSignal_bound_of_expansion_actual {U : Type} [Fintype U]
    (v : InfinitePlace F) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ sourceHilbertSet F S₀)
    (A : Classes → SourceReflectionExpansionData F S₀ U)
    (hA : SourceReflectionLiteralExpansion F S₀ hζ η hBad A) :
    principalAngularGaussianSignal hζ η (sourceHilbertSet F S₀) =O[atTop]
      (fun Z : ℝ => Z ^ (7 / 15 - 1 / 20000 : ℝ)) :=
  sourcePoissonAngularSignal_bound_of_reflected F S₀ hζ η v hBad hJ hcut
    (sourcePoissonReflectedSecondMoment_of_expansion_actual F S₀ hζ η hBad A hA)

end
end ArtinMatthews.SourceEulerAssembly
