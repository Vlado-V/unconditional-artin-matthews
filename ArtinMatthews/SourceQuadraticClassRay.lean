module

public import ArtinMatthews.SourceQuadraticClassProjection
public import ArtinMatthews.HeckeExtension.SourceSupportedRay


set_option backward.privateInPublic true
@[expose] public section

/-! The fixed allowed-generator square classes factor through the
genuine finite ideal ray quotient at the S-supported Hensel modulus. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain FractionalIdeal ClassFieldTheory RayClass
open AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀

abbrev sourceQuadraticFixedModulus : Modulus F :=
  integralIdealRayModulus (sixthKummerFixedIdeal S) (sixthKummerFixedIdeal_ne_zero S)

abbrev SourceQuadraticRayClass := IdealRayClassGroup (sourceQuadraticFixedModulus F S₀)

theorem sourceQuadraticFixedModulus_support :
    (sourceQuadraticFixedModulus F S₀).finitePart.support = S :=
  sixthKummerFixedIdeal_support F S

theorem sourceQuadraticFixedModulus_depth (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S) :
    sixthLocalHenselDepth v ≤ (sourceQuadraticFixedModulus F S₀).finitePart v := by
  apply (FiniteMultiplicity.of_prime_left v.prime
    (sixthKummerFixedIdeal_ne_zero S)).le_multiplicity_of_pow_dvd
  exact Finset.dvd_prod_of_mem (fun p : HeightOneSpectrum (𝓞 F) =>
    p.asIdeal ^ sixthLocalHenselDepth p) hv

theorem sourceQuadraticRayClass_finite : Finite (SourceQuadraticRayClass F S₀) :=
  Finite.of_equiv (RayClassGroup (sourceQuadraticFixedModulus F S₀))
    (rayClassGroupEquivIdealRayClassGroup (sourceQuadraticFixedModulus F S₀)).toEquiv

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceComplementGlobalIdealClass_principal_ray (a : Fˣ)
    (ha : IdeleGroup.principalIdele F a ∈
      idelePrimeToModulusSubgroup (sourceQuadraticFixedModulus F S₀)) :
    sourceComplementGlobalIdealClass F S₀ hζ (toPrincipalIdeal (𝓞 F) F a) = 1 := by
  rw [sourceComplementGlobalIdealClass_principal]
  have hfinite : sLocalGlobalClassMap F 6 S a = 1 := by
    funext v
    have hv : v.val ∈ (sourceQuadraticFixedModulus F S₀).finitePart.support := by
      rw [sourceQuadraticFixedModulus_support]
      exact v.property
    have hu := localHigherUnitGroup_antitone v.val
      (sourceQuadraticFixedModulus_depth F S₀ v.val v.property) (ha.2 v.val hv)
    obtain ⟨w, hw⟩ := sixthLocal_higherUnit_exists_root v.val _ hu
    exact (QuotientGroup.eq_one_iff _).mpr ⟨w, hw⟩
  let := source_isTotallyComplex F hζ
  have hwhole := sLocalRingGlobalClass_eq_one_of_finite F 6 S a hfinite
  change sourceComplementClassProjection F S₀ hζ (sLocalRingGlobalClassMap F 6 S a) = 1
  rw [hwhole, map_one]

theorem sourceQuadraticIdealClass_principal_ray (a : Fˣ)
    (ha : IdeleGroup.principalIdele F a ∈
      idelePrimeToModulusSubgroup (sourceQuadraticFixedModulus F S₀)) :
    sourceQuadraticIdealClass F S₀ hζ (toPrincipalIdeal (𝓞 F) F a) = 1 := by
  change sourceComplementSquareClass F S₀ hζ
    (sourceComplementGlobalIdealClass F S₀ hζ (toPrincipalIdeal (𝓞 F) F a)) = 1
  rw [sourceComplementGlobalIdealClass_principal_ray F S₀ hζ a ha, map_one]

def sourceComplementRayClass : SourceQuadraticRayClass F S₀ →* chosenB F hζ S₀ :=
  QuotientGroup.lift (principalRayIdealSubgroup (sourceQuadraticFixedModulus F S₀))
    ((sourceComplementGlobalIdealClass F S₀ hζ).comp
      (primeToModulusIdeals (sourceQuadraticFixedModulus F S₀)).subtype) (by
        intro I hI
        obtain ⟨a, ha, he⟩ := (mem_principalRayIdealSubgroup_iff _ I).mp hI
        change sourceComplementGlobalIdealClass F S₀ hζ (I : FractionalIdealGroup F) = 1
        rw [← he]
        exact sourceComplementGlobalIdealClass_principal_ray F S₀ hζ a ha)

@[simp] theorem sourceComplementRayClass_ideal
    (I : primeToModulusIdeals (sourceQuadraticFixedModulus F S₀)) :
    sourceComplementRayClass F S₀ hζ
        (QuotientGroup.mk' (principalRayIdealSubgroup (sourceQuadraticFixedModulus F S₀)) I) =
      sourceComplementGlobalIdealClass F S₀ hζ (I : FractionalIdealGroup F) := rfl

def sourceQuadraticRayClassMap : SourceQuadraticRayClass F S₀ →* SLocalPowerClasses F 2 S :=
  (sourceComplementSquareClass F S₀ hζ).comp (sourceComplementRayClass F S₀ hζ)

@[simp] theorem sourceQuadraticRayClassMap_ideal
    (I : primeToModulusIdeals (sourceQuadraticFixedModulus F S₀)) :
    sourceQuadraticRayClassMap F S₀ hζ
        (QuotientGroup.mk' (principalRayIdealSubgroup (sourceQuadraticFixedModulus F S₀)) I) =
      sourceQuadraticIdealClass F S₀ hζ (I : FractionalIdealGroup F) := rfl

end
end ArtinMatthews.SourceEulerAssembly
