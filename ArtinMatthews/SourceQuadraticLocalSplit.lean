module

public import ArtinMatthews.ArtinRaySplitCoefficient
public import ArtinMatthews.SourceQuadraticConductorProduct


set_option backward.privateInPublic true
@[expose] public section

/-! A square in the actual completed base field gives coefficient one
for the source quadratic character at that prime. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic AngularLambda
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceQuadraticRayCharacter_prime_of_localSquare
    (e : SourcePrimeExponents F S₀) (P : HeightOneSpectrum (𝓞 F))
    (hsquare : ∃ s : P.adicCompletion F,
      s ^ 2 = algebraMap F (P.adicCompletion F) (sourcePrimeExponentUnit F hζ S₀ e : F)) :
    (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient P.asIdeal = 1 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let : IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) :=
    sourceQuadraticField_isAbelianGalois F S₀ hζ e
  exact ArtinRay.abelianNormConductorRayCharacter_prime_of_splitsCompletely
    (sourceQuadraticGaloisCharacter F S₀ hζ e) P
    (quadraticKummer_finitePlaceSplitsCompletely_of_localSquare
      (sourcePrimitiveRootSix F hζ) (sourcePrimeExponentUnit F hζ S₀ e) P hsquare)

end
end ArtinMatthews.SourceEulerAssembly
