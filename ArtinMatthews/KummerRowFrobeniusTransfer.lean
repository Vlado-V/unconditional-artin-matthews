module

public import ArtinMatthews.KummerRowTowerRestriction
public import ArtinMatthews.KummerRowRayCharacters


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Frobenius ideal values of a common Kummer row agree with
those of the individual degree-dividing-six extension. The comparison is
proved on every ideal prime to the preserved coarse common modulus. -/
namespace ArtinMatthews
open NumberField VaryingKummerAnalytic IsDedekindDomain
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]

theorem sixthKummerRow_idealHom_eq_individual_of_discriminant_support
    {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0)
    (I : FractionalIdealGroup F)
    (hI : ∀ v : HeightOneSpectrum (𝓞 F), FractionalIdeal.count F v I.val ≠ 0 →
      ((NumberField.discr (sixthKummerRowField A)).natAbs : 𝓞 F) ∉ v.asIdeal) :
    GaloisIdealCharacter.idealHom F (sixthKummerRowField A)
        (sixthKummerRowCharacter hζ A a ha ha0) I=
      GaloisIdealCharacter.idealHom F (sixthKummerRowField {a})
        (sixthKummerRowCharacter hζ {a} a (Finset.mem_singleton_self _) ha0) I := by
  let := sixthKummerIndividualAlgebra A a ha
  let : IsScalarTower F (sixthKummerRowField {a}) (sixthKummerRowField A) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := sixthKummerRowField_isAbelianGalois hζ {a}
  let := sixthKummerRowField_isAbelianGalois hζ A
  rw [← sixthKummerRowCharacter_eq_individual_comp hζ A a ha ha0]
  exact ArtinRay.idealHom_comp_restrict_of_discriminant_support _ I hI

variable [NumberField.IsTotallyComplex F]

theorem sixthKummerRow_rayIdealHom_eq_individual {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (A : Finset F) (a : F) (ha : a ∈ A) (ha0 : a ≠ 0)
    (I : RayClass.primeToModulusIdeals (rationalIdealRayModulus F
      (discriminantDegreeModulus F (sixthKummerRowField A)))) :
    (sixthKummerRowRayCharacter hζ A a ha ha0).idealHom (I:FractionalIdealGroup F)=
      (sixthKummerRowRayCharacter hζ {a} a (Finset.mem_singleton_self _) ha0).idealHom
        (I:FractionalIdealGroup F) := by
  rw [sixthKummerRowRayCharacter_idealHom,sixthKummerRowRayCharacter_idealHom]
  apply sixthKummerRow_idealHom_eq_individual_of_discriminant_support hζ A a ha ha0
  intro v hv hD
  have hN : (discriminantDegreeModulus F (sixthKummerRowField A) : 𝓞 F) ∈ v.asIdeal := by
    rw [discriminantDegreeModulus,Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hD
  have hd : v.asIdeal ∣ rationalModulusIdeal (𝓞 F)
      (discriminantDegreeModulus F (sixthKummerRowField A)) :=
    Ideal.dvd_span_singleton.mpr hN
  exact hv (I.property v ((integralIdealFiniteModulus_mem_support _
    (rationalModulusIdeal_ne_bot _) v).mpr hd))

end
end ArtinMatthews
