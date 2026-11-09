module

public import ArtinMatthews.ArtinRaySmallModulus
public import ArtinMatthews.VaryingKummerAnalyticRayCharacterMultiplicityCount


set_option backward.privateInPublic true
@[expose] public section

/-! Faithfulness of the actual finite abelian Frobenius family on coprime
ideal coefficients. The proof uses the genuine Artin-map nonprincipality
theorem and introduces no prime-distribution or zero-exclusion input. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open scoped NumberField nonZeroDivisors Classical
noncomputable section

namespace GaloisIdealCharacter
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem idealHom_div (χ θ : Gal(L/K) →* ℂˣ) (I : FractionalIdealGroup K) :
    idealHom K L (χ/θ) I = idealHom K L χ I / idealHom K L θ I := by
  unfold idealHom
  simp only [MonoidHom.div_apply,div_zpow]
  exact finprod_div_distrib (finite_factor_support K L χ I) (finite_factor_support K L θ I)

end GaloisIdealCharacter

namespace ArtinRay
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]

theorem discriminantDegreeRayCharacter_coefficient_injective :
    Function.Injective (fun χ : Gal(L/K) →* ℂˣ =>
      (discriminantDegreeRayCharacter (K := K) (L := L) χ).coefficient) := by
  intro χ θ hcoeff
  by_contra hne
  have hdiv : χ/θ ≠ 1 := fun h => hne (div_eq_one.mp h)
  obtain ⟨I,hI,hcop,hvalue⟩ := discriminantDegreeRayCharacter_isNonprincipal (χ/θ) hdiv
  apply hvalue
  have he := (EvenRayCharacter.agreesOnCoprimeIdeals_iff_coefficient_eq
    (discriminantDegreeRayCharacter (K := K) (L := L) χ)
    (discriminantDegreeRayCharacter (K := K) (L := L) θ)).mpr hcoeff I hI hcop
  rw [discriminantDegreeRayCharacter_idealHom,discriminantDegreeRayCharacter_idealHom] at he
  rw [discriminantDegreeRayCharacter_idealHom,GaloisIdealCharacter.idealHom_div,he]
  simp

end ArtinRay
end
end ArtinMatthews.VaryingKummerAnalytic
