module

public import ArtinMatthews.SourceQuadraticScaleEnlargement
public import ArtinMatthews.SourceQuadraticSieveReflection


set_option backward.privateInPublic true
@[expose] public section

/-! The checked analytic interface between the Poisson-scale bound and
the exterior sieve used by the actual reflected square moment. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceReflectionQuadraticSieve_of_poisson
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hpoisson : ∀ a : ℝ, 1 < a →
      QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) a →
      QuadraticHeckePoissonScaleBound (sourceQuadraticDyadicEnergy F S₀ hζ) a) :
    SourceReflectionQuadraticSieve F S₀ hζ :=
  sourceReflectionQuadraticSieve_of_exponent_one F S₀ hζ htrace
    (sourceQuadraticDyadicEnergy_exponent_one_of_poisson F S₀ hζ htrace hpoisson)

end ArtinMatthews.SourceEulerAssembly
