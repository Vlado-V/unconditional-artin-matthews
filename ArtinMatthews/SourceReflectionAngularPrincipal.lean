module

public import ArtinMatthews.SourceReflectionAngularIdeal
public import ArtinMatthews.VaryingKummerAnalyticRayCharacterQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! Clear denominators inside the actual ray, then apply the integral
Eisenstein angular law to both the numerator and the denominator. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain RayClass AngularLambda SIntegerPrincipalization
open scoped NumberField Classical nonZeroDivisors

noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem sourceReflection_exists_fraction_congr_one
    (M : Ideal (𝓞 F)) (hM : M ≠ ⊥) (a : Fˣ)
    (ha : IdeleGroup.principalIdele F a ∈
      idelePrimeToModulusSubgroup (integralIdealRayModulus M hM)) :
    ∃ A b : 𝓞 F, A ≠ 0 ∧ b ≠ 0 ∧ A - 1 ∈ M ∧ b - 1 ∈ M ∧
      (a : F) = (A : F) / (b : F) := by
  by_cases htop : M = ⊤
  · obtain ⟨A,b,hA,hb,hab⟩ := exists_nonzero_integral_fraction F a
    exact ⟨A,b,hA,hb,htop ▸ Submodule.mem_top,htop ▸ Submodule.mem_top,hab⟩
  have hD := rayFractionalDenominatorIdeal_coprime F M hM (a : F)
    (fun v hv => (principal_idealRayModulus_valuation_one M hM a ha v hv).le)
  obtain ⟨b,hbD,c,hcM,hbc⟩ := Ideal.isCoprime_iff_exists.mp hD
  have hb1 : b - 1 ∈ M := by
    have he : b - 1 = -c := by rw [← hbc]; ring
    rw [he]
    exact M.neg_mem hcM
  have hb0 : b ≠ 0 := by
    intro hz
    have h1 : (1 : 𝓞 F) ∈ M := by
      simpa only [hz, zero_sub, neg_neg] using M.neg_mem hb1
    exact htop ((Ideal.eq_top_iff_one M).mpr h1)
  obtain ⟨A,hAb⟩ := hbD
  have hbF : (b : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb0
  have hAF : (A : F) ≠ 0 := by rw [← hAb]; exact mul_ne_zero a.ne_zero hbF
  have hd := principal_idealRayModulus_integral_difference M hM a ha A b
    (mul_comm (b : F) (a : F) |>.trans hAb)
  have hA1 : A - 1 ∈ M := by
    convert M.add_mem hd hb1 using 1
    ring
  exact ⟨A,b,RingOfIntegers.coe_ne_zero_iff.mp hAF,hb0,hA1,hb1,(eq_div_iff hbF).mpr hAb⟩

variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
local notation "M" => sourceReflectionAngularModulus F S₀
local notation "hM" => sourceReflectionAngularModulus_ne_bot F S₀
local notation "n" => integralIdealFiniteModulus M hM

theorem sourceReflectionAngularIdealHom_congr_one (A : 𝓞 F) (hA : A ≠ 0)
    (hA1 : A - 1 ∈ M) :
    sourceReflectionAngularIdealHom F hζ S₀
        (integralIdealFractionalUnit (Ideal.span {A}) (by simpa using hA)) =
      sourceReflectionAngularField F hζ (Units.mk0 (A : F)
        (RingOfIntegers.coe_ne_zero_iff.mpr hA)) := by
  have hI : Ideal.span {A} ∈ exteriorIdeals
      (principalizingDenominator (sourceHilbertSeed F S₀)) := by
    apply (exteriorIdeals_mem_iff (sourceHilbertSeed F S₀) _).mpr
    refine ⟨by simpa using hA, ?_⟩
    intro P hP hd
    have hdM : P.asIdeal ∣ M := (integralIdealFiniteModulus_mem_support M hM P).mp
      (sourceReflectionAngularModulus_support F S₀ ▸ hP)
    have hA' : A ∈ P.asIdeal := Ideal.dvd_span_singleton.mp hd
    have h1 : (1 : 𝓞 F) ∈ P.asIdeal := by
      have h := P.asIdeal.sub_mem hA' ((Ideal.dvd_iff_le.mp hdM) hA1)
      rwa [sub_sub_cancel] at h
    exact P.prime.not_isUnit (by rw [(Ideal.eq_top_iff_one _).mpr h1, ← Ideal.one_eq_top]; exact isUnit_one)
  have h3 : (3 : 𝓞 F) ∣ A - 1 := Ideal.mem_span_singleton.mp
    (Ideal.mul_le_left hA1)
  apply Units.ext
  rw [sourceReflectionAngularIdealHom_integral_eq_of_exterior F hζ S₀ _ hI]
  letI : Algebra BaseField F := baseAlgebraOfTwelve hζ
  rw [sourceReflectionAngularField_val F hζ]
  exact angularNormIdeal_principal_archimedean F A hA h3

theorem sourceReflectionAngularIdealHom_exterior_eq_field_of_deep (a : Fˣ)
    (ha : sourceReflectionFiniteDiagonal F S a ∈ sourceReflectionDeepUnits F S n) :
    sourceReflectionAngularIdealHom F hζ S₀
        (IdeleGroup.fractionalIdeal (sourceReflectionExteriorIdele F S a)) =
      sourceReflectionAngularField F hζ a := by
  have hp := sourceReflectionPrincipalIdele_mem_primeTo_of_deep F S n
    (sourceReflectionAngularModulus_support F S₀).le a ha
  have hu : ∀ P : S, sourceReflectionFiniteDiagonal F S a P ∈
      (P.val.adicCompletionIntegers F).units :=
    fun P => localHigherUnitGroup_le_integralUnits P.val (n P.val)
      ((sourceReflectionDeepUnits_mem_iff F S n _).mp ha P)
  obtain ⟨A,b,hA,hb,hA1,hb1,hab⟩ := sourceReflection_exists_fraction_congr_one F M hM a hp
  rw [sourceReflectionExteriorIdele_ideal_eq_principal_of_localUnits F S a hu,
    toPrincipalIdeal_eq_fraction a A b hA hb hab, map_div,
    sourceReflectionAngularIdealHom_congr_one F hζ S₀ A hA hA1,
    sourceReflectionAngularIdealHom_congr_one F hζ S₀ b hb hb1, ← map_div]
  congr 1
  apply Units.ext
  simpa only [Units.val_div_eq_div_val, Units.val_mk0] using hab.symm

end
end ArtinMatthews.VaryingKummerAnalytic
