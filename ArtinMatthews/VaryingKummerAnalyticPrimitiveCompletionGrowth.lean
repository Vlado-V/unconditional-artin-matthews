module

public import ArtinMatthews.VaryingKummerAnalyticPrimitiveCompletion
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine subquadratic growth of the canonical proper Hecke completion. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField ArtinMatthews.ReusedGrowth
open scoped NumberField nonZeroDivisors Classical
noncomputable section
namespace EvenIdealRayCharacter
variable {K : Type*} [Field K] [NumberField K] {M : Ideal (𝓞 K)}
variable (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) (hMt : M ≠ ⊤)

theorem properCompleted_hasSubquadraticGrowth
    (hprim : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals ψ.residue) :
    HasSubquadraticGrowth (ψ.properCompleted hM hMt) :=
  ψ.scaledGeneratorCompletedMellin_hasSubquadraticGrowth hM
    (primitiveClassGenerator K M hM hMt) (primitiveClassGenerator_ne_bot K M hM hMt)
    (fun h => hMt (idealConductor_top_of_primitive_residue_one ψ.residue hprim h))
    (mixedConductorScale_pos K (integralIdealFractionalUnit M hM))

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
