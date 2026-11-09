module

public import ArtinMatthews.IdealRayCharacterProduct
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity


set_option backward.privateInPublic true
@[expose] public section

/-! Literal ideal coefficients of a product-modulus character, including
the bad-prime masks. Inversion is complex conjugation on finite-order
ideal values, so the fixed twist has coefficients η(I) conjugate(χ(I)). -/
namespace ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {M N : Ideal (𝓞 K)}

theorem multiplyAtProduct_allCoefficient (η : EvenIdealRayCharacter K M)
    (ψ : EvenIdealRayCharacter K N) (hM : M ≠ ⊥) (hN : N ≠ ⊥) (I : Ideal (𝓞 K)) :
    (η.multiplyAtProduct ψ hM hN).allCoefficient I = η.allCoefficient I * ψ.allCoefficient I := by
  by_cases hI : I = ⊥
  · subst I
    simp only [allCoefficient_bot,zero_mul]
  simp only [allCoefficient,dite_eq_left hI,IsCoprime.mul_right_iff]
  by_cases hcM : IsCoprime I M
  · by_cases hcN : IsCoprime I N
    · simp only [hcM,hcN,and_self,ite_true,multiplyAtProduct_idealHom,Units.val_mul]
    · simp only [hcM,hcN,and_false,ite_false,ite_true,mul_zero]
  · simp only [hcM,false_and,ite_false,zero_mul]

theorem inverse_allCoefficient_conj (ψ : EvenIdealRayCharacter K M) (I : Ideal (𝓞 K)) :
    ψ.inverse.allCoefficient I = starRingEnd ℂ (ψ.allCoefficient I) := by
  by_cases hI : I = ⊥
  · subst I
    simp only [allCoefficient_bot,map_zero]
  rw [ψ.inverse.allCoefficient_eq_coefficient I hI,ψ.allCoefficient_eq_coefficient I hI]
  exact ψ.inverse_coefficient_conj _

theorem twistInverseAtProduct_allCoefficient (η : EvenIdealRayCharacter K M)
    (ψ : EvenIdealRayCharacter K N) (hM : M ≠ ⊥) (hN : N ≠ ⊥) (I : Ideal (𝓞 K)) :
    (η.twistInverseAtProduct ψ hM hN).allCoefficient I =
      η.allCoefficient I * starRingEnd ℂ (ψ.allCoefficient I) := by
  rw [twistInverseAtProduct,multiplyAtProduct_allCoefficient,inverse_allCoefficient_conj]

end
end ArtinMatthews.VaryingKummerAnalytic.EvenIdealRayCharacter
