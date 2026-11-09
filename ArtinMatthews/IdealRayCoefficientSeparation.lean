module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity


set_option backward.privateInPublic true
@[expose] public section

/-! Equality of full coefficient functions implies equality of ideal
values only where both actual conductor masks are nonzero. -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
open NumberField
open scoped NumberField nonZeroDivisors
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem idealHom_eq_of_coefficient_eq_of_coprime {M f : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (φ : EvenIdealRayCharacter K f)
    (he : ψ.coefficient=φ.coefficient) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hM : IsCoprime I M) (hf : IsCoprime I f) :
    ψ.idealHom (integralIdealFractionalUnit I hI)=φ.idealHom (integralIdealFractionalUnit I hI) := by
  have hc : ψ.allCoefficient I=φ.allCoefficient I :=
    (ψ.allCoefficient_eq_coefficient I hI).trans
      ((congrFun he _).trans (φ.allCoefficient_eq_coefficient I hI).symm)
  simp only [allCoefficient,dite_eq_left hI,ite_eq_left hM,ite_eq_left hf] at hc
  exact Units.ext hc

end
end ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
