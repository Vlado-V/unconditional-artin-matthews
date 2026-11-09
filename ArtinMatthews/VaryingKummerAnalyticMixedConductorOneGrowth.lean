module

public import ArtinMatthews.VaryingKummerAnalyticMixedConductorOneFunctionalEquation
public import ArtinMatthews.VaryingKummerAnalyticMixedClassGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Subquadratic growth of the actual conductor-one completion, with the
same discriminant normalization as its inverse-character functional equation. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField ArtinMatthews.ReusedGrowth
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hMtop : M = ⊤)

theorem conductorOneCompleted_hasSubquadraticGrowth :
    HasSubquadraticGrowth (ψ.conductorOneCompleted hMtop) :=
  scaledMixedEntireIdealClassCompletion_hasSubquadraticGrowth K
    (ψ.conductorOneClassCharacter hMtop) (mixedDiscriminantScale_pos K)

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
