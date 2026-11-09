module

public import ArtinMatthews.SourceReflectionLocalThetaCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Exact angular and retained finite ray evaluation of the literal
reflected coefficient at the original allowed generators. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain AngularLambda AllowedGenerators QuadraticWeil
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
variable {J : Ideal (𝓞 F)}
local notation "hG" => mul_ne_zero (sixthKummerFixedIdeal_ne_zero S) (sixthKummerFixedIdeal_ne_zero S)

theorem sourceReflectionAngularField_inv_place_product (a : Fˣ) :
    ((sourceReflectionAngularField F hζ a)⁻¹ : ℂˣ).val =
      ∏ v : InfinitePlace F, complexAngular (v.embedding (a:F)) ^
        (-sourceReflectionAngularInfinityExponent F hζ v) := by
  rw [Units.val_inv_eq_inv_val, sourceReflectionAngularField_place_product F hζ,
    ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro v _
  exact (zpow_neg _ _).symm

theorem sourceReflectionThetaValue_eq_local_mul_arch
    (hBad : standardWeilBadPlaces F ⊆ S) (η : EvenIdealRayCharacter F J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ S) (e : SourcePrimeExponents F S₀) :
    let a := sourcePrimeExponentUnit F hζ S₀ e
    reflectionThetaValue F hζ S₀ hBad η e =
      (sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η
        (sourceReflectionFiniteDiagonal F S a) : ℂ) *
      ∏ v : InfinitePlace F, complexAngular (v.embedding (a:F)) ^
        (-sourceReflectionAngularInfinityExponent F hζ v) := by
  let gauss : EvenIdealRayCharacter F (sixthKummerFixedIdeal S * sixthKummerFixedIdeal S) :=
    @sourceGaussHeckeCharacter F _ _ _ ζ hζ S₀ hBad
  let a := sourcePrimeExponentUnit F hζ S₀ e
  let u := sourceReflectionFiniteDiagonal F S a
  let I := sourcePrimeExponentIdeal F S₀ e
  let hI : I ≠ ⊥ := sourcePrimeExponentIdeal_ne_bot F S₀ e
  let D := integralIdealFractionalUnit I hI
  let A := sourceReflectionAngularField F hζ a
  let L := sourceReflectionAngularIdealHom F hζ S₀ D
  let g := sourceReflectionLocalRayCharacter F S gauss hG u
  let r := sourceReflectionLocalRayCharacter F S η hJ u
  let χ := sourceReflectionLocalThetaCharacter F S₀ hJ hζ hBad η
  have hD : IdeleGroup.fractionalIdeal (sourceReflectionExteriorIdele F S a) = D :=
    sourceReflectionExteriorIdele_primeExponentIdeal F hζ S₀ e
  have hJSupp := sourceReflectionTargetModulus_support F S₀ hJ hcut
  have hL : (L : ℂ) = cyclotomicAngularIdeal hζ I :=
    sourceReflectionAngularIdealHom_primeExponentIdeal F hζ S₀ e
  have hγ : gauss.idealHom D = g⁻¹ := by
    rw [← hD]
    exact sourceReflectionIdealRay_exteriorPrincipal F S gauss hG
      (sourceReflectionGaussModulus_support F S₀).le a
  have hη : η.allCoefficient I = (r⁻¹ : ℂˣ).val := by
    have hc : IsCoprime I J := sourcePrimeExponentIdeal_coprime_of_modulusSupport F S₀ hJ hJSupp e
    rw [EvenIdealRayCharacter.allCoefficient, dite_eq_left hI, ite_eq_left hc]
    change (η.idealHom D : ℂ) = _
    rw [← hD, sourceReflectionIdealRay_exteriorPrincipal F S η hJ hJSupp]
  have hC : sourceReflectionLocalAngularCharacter F hζ S₀ u = A / L := by
    change sourceReflectionLocalAngularCharacter F hζ S₀ (sourceReflectionFiniteDiagonal F S a) = _
    rw [sourceReflectionLocalAngularCharacter_diagonal, sourceReflectionAngularFieldCorrection,
      MonoidHom.div_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hD]
  have hStarL : star (L : ℂ) = (L⁻¹ : ℂˣ).val := by
    rw [Complex.star_def, Units.val_inv_eq_inv_val,
      Complex.inv_eq_conj (sourceReflectionAngularIdealHom_norm F hζ S₀ D)]
  have hInvg : (g⁻¹ : ℂˣ).val = star (g : ℂ) := by
    rw [Complex.star_def, Units.val_inv_eq_inv_val,
      Complex.inv_eq_conj (sourceReflectionLocalRayCharacter_norm F S gauss hG u)]
  have hχ : χ u = sourceReflectionLocalAngularCharacter F hζ S₀ u * g / r := rfl
  have hUnits : L⁻¹ * g * r⁻¹ = χ u * A⁻¹ := by
    rw [hχ, hC]
    simp only [div_eq_mul_inv]
    calc
      _ = (A * A⁻¹) * (L⁻¹ * g * r⁻¹) := by simp
      _ = (A * (L⁻¹ * g * r⁻¹)) * A⁻¹ := by
        rw [mul_assoc A A⁻¹, mul_comm A⁻¹, ← mul_assoc]
      _ = _ := by simp only [mul_assoc]
  change star (cyclotomicAngularIdeal hζ I) * star (gauss.idealHom D : ℂ) * η.allCoefficient I =
    (χ u : ℂ) * ∏ v : InfinitePlace F, complexAngular (v.embedding (a:F)) ^
      (-sourceReflectionAngularInfinityExponent F hζ v)
  calc
    _ = ((L⁻¹ * g * r⁻¹ : ℂˣ) : ℂ) := by
      rw [← hL, hγ, hη, hStarL, hInvg, star_star]
      rfl
    _ = _ := by
      rw [hUnits, Units.val_mul, sourceReflectionAngularField_inv_place_product F hζ a]

end
end ArtinMatthews.VaryingKummerAnalytic
