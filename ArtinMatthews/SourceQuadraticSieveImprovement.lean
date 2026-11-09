module

public import ArtinMatthews.SourceQuadraticPoissonReduction
public import ArtinMatthews.SourceQuadraticScaleEnlargement


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit improved exponent for the actual exterior energy,
derived from the annular B3 estimate at the original exponent. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {G : Type} [Fintype G] [DecidableEq G]

theorem sourceQuadraticDyadicEnergy_improve_of_B3
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (label : SourcePrimeExponents F S₀ → G) {a : ℝ} (ha : 1 < a)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) a)
    (hB3 : SourceQuadraticB3PoissonBound F S₀ hζ label a) :
    QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) (2 - a⁻¹) := by
  obtain ⟨A, hA, hscale⟩ := sourceQuadraticDyadicEnergy_enlarge F S₀ hζ htrace
  exact quadraticHeckeSieveExponentBound_of_poisson_scale
    (sourceQuadraticDyadicEnergy F S₀ hζ) ha A hA (2 * Module.finrank ℚ F) hscale
    (sourceQuadraticPoissonScaleBound_of_B3 F S₀ hζ label ha hE hB3)

end ArtinMatthews.SourceEulerAssembly
