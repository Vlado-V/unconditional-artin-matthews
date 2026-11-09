module

public import ArtinMatthews.SourceQuadraticActualB3
public import ArtinMatthews.SourceQuadraticSieveImprovement
public import ArtinMatthews.SourceQuadraticSieveFromB3
public import ArtinMatthews.SourceQuadraticClassRay


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain StandardAdelic
open scoped NumberField
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

/-- Actual exponent improvement from the proved source B3 estimate. -/
theorem sourceQuadraticDyadicEnergy_improve_actual
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀) {α : ℝ} (hα : 1 < α)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α) :
    QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) (2 - α⁻¹) := by
  classical
  let : Finite (SourceQuadraticRayClass F S₀) := sourceQuadraticRayClass_finite F S₀
  let := Fintype.ofFinite (SourceQuadraticRayClass F S₀)
  exact sourceQuadraticDyadicEnergy_improve_of_B3 F S₀ hζ htrace
    (sourcePrimeExponentRayClass F S₀) hα hE
    (sourceQuadraticB3PoissonBound_actual F S₀ hζ htrace hα.le hE)

/-- The sharp quadratic sieve for the actual source family.  All Poisson,
contour, signed-residue and tail estimates are discharged above. -/
theorem sourceReflectionQuadraticSieve_actual
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀) :
    SourceReflectionQuadraticSieve F S₀ hζ := by
  classical
  let : Finite (SourceQuadraticRayClass F S₀) := sourceQuadraticRayClass_finite F S₀
  let := Fintype.ofFinite (SourceQuadraticRayClass F S₀)
  exact sourceReflectionQuadraticSieve_of_B3 F S₀ hζ htrace
    (sourcePrimeExponentRayClass F S₀) fun _ hα hE =>
      sourceQuadraticB3PoissonBound_actual F S₀ hζ htrace hα.le hE

end
end ArtinMatthews.SourceEulerAssembly
