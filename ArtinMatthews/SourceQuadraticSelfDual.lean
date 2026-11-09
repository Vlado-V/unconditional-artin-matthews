module

public import ArtinMatthews.SourceQuadraticPrimitive


set_option backward.privateInPublic true
@[expose] public section

/-! Literal self-duality of the actual primitive source characters,
including their conductor-zero masks. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceQuadraticRayCharacter_star_idealHom (e : SourcePrimeExponents F S₀)
    (I : FractionalIdealGroup F) :
    star ((sourceQuadraticRayCharacter F S₀ hζ e).idealHom I : ℂ) =
      ((sourceQuadraticRayCharacter F S₀ hζ e).idealHom I : ℂ) := by
  have h : ((sourceQuadraticRayCharacter F S₀ hζ e).idealHom I : ℂ) ^ 2 = 1 :=
    congrArg Units.val (sourceQuadraticRayCharacter_sq F S₀ hζ e I)
  rcases sq_eq_one_iff.mp h with heq | heq
  · rw [heq, star_one]
  · rw [heq, star_neg, star_one]

theorem sourceQuadraticRayCharacter_star_allCoefficient (e : SourcePrimeExponents F S₀)
    (I : Ideal (𝓞 F)) :
    star ((sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient I) =
      (sourceQuadraticRayCharacter F S₀ hζ e).allCoefficient I := by
  unfold EvenIdealRayCharacter.allCoefficient
  split_ifs
  · exact sourceQuadraticRayCharacter_star_idealHom F S₀ hζ e _
  · exact star_zero _
  · exact star_zero _

end
end ArtinMatthews.SourceEulerAssembly
