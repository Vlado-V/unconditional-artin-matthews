module

public import ArtinMatthews.SourceQuadraticPoissonReduction
public import ArtinMatthews.SourceQuadraticSieveFromPoisson


set_option backward.privateInPublic true
@[expose] public section

/-! The analytic B3 estimate is the remaining input to the literal
sharp quadratic large sieve and the reflected-moment application. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {G : Type} [Fintype G] [DecidableEq G]

theorem sourceReflectionQuadraticSieve_of_B3
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (label : SourcePrimeExponents F S₀ → G)
    (hB3 : ∀ a : ℝ, 1 < a →
      QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) a →
      SourceQuadraticB3PoissonBound F S₀ hζ label a) :
    SourceReflectionQuadraticSieve F S₀ hζ :=
  sourceReflectionQuadraticSieve_of_poisson F S₀ hζ htrace fun a ha hE =>
    sourceQuadraticPoissonScaleBound_of_B3 F S₀ hζ label ha hE (hB3 a ha hE)

end ArtinMatthews.SourceEulerAssembly
