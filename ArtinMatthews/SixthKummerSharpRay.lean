module

public import ArtinMatthews.SixthKummerSharpModulus
public import ArtinMatthews.KummerRowUnramified
public import ArtinMatthews.SixthKummerLocalNorm
public import ArtinMatthews.ArtinRayIdealLocalNorm
public import ArtinMatthews.ArtinRayNonprincipal
public import ArtinMatthews.VaryingKummerAnalyticRayIdealConductorOne


set_option backward.privateInPublic true
@[expose] public section

/-! The literal sharp ideal modulus of an individual sixth-Kummer
character. All local norm and unramified support conditions are discharged
from the radicand valuations, Hensel lifting and actual inertia. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
include hζ

theorem sixthKummerSharpIdeal_unramified_outside
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : sixthWildPrimes F ⊆ S) (u : Fˣ)
    (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ (integralIdealFiniteModulus (sixthKummerSharpIdeal S u)
      (sixthKummerSharpIdeal_ne_zero S u)).support) :
    Algebra.IsUnramifiedAt (𝓞 F)
      (GaloisIdealCharacter.primeAbove F (sixthKummerRowField {(u:F)}) v).val := by
  have hnot : ¬v.asIdeal ∣ sixthKummerSharpIdeal S u :=
    mt (integralIdealFiniteModulus_mem_support (sixthKummerSharpIdeal S u)
      (sixthKummerSharpIdeal_ne_zero S u) v).mpr hv
  have hvS : v ∉ S := by
    intro h
    apply hnot
    exact (dvd_pow_self _ (sixthLocalHenselDepth_pos v).ne').trans
      (sixthKummerSharpIdeal_fixed_pow_dvd S u v h)
  have hu : exteriorPrincipalValuation v u=0 := by
    by_contra hu
    exact hnot (sixthKummerSharpIdeal_radical_dvd S u v hvS hu)
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hvS (hS ((mem_sixthWildPrimes v).mpr h))
  let Q := GaloisIdealCharacter.primeAbove F (sixthKummerRowField {(u:F)}) v
  let : Q.val.IsPrime := Q.property.1
  let : Q.val.IsMaximal := Q.property.1.isMaximal
    (GaloisIdealCharacter.primeAbove_ne_bot F (sixthKummerRowField {(u:F)}) v)
  exact sixthKummerIndividual_unramifiedAt hζ u v h6 hu Q.val Q.property.2.over.symm

theorem sixthKummerSharpIdeal_localNorm
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : sixthWildPrimes F ⊆ S) (u : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    RayClass.localHigherUnitGroup v (integralIdealFiniteModulus (sixthKummerSharpIdeal S u)
      (sixthKummerSharpIdeal_ne_zero S u) v) ≤
      chosenFinitePlaceLocalNormSubgroup (K := F) (L := sixthKummerRowField {(u:F)}) v := by
  by_cases hvS : v ∈ S
  · exact (RayClass.localHigherUnitGroup_antitone v
      (sixthKummerSharpIdeal_fixed_depth_le S u v hvS)).trans
        (sixthKummerIndividual_higherUnit_le_chosenLocalNorm hζ (u:F) u.ne_zero v)
  · have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hvS (hS ((mem_sixthWildPrimes v).mpr h))
    by_cases hu : exteriorPrincipalValuation v u=0
    · let w := chosenFinitePlaceExtension (L := sixthKummerRowField {(u:F)}) v
      let Q := finitePlaceExtensionCentre (K := F) (L := sixthKummerRowField {(u:F)}) v w
      have hQ := finitePlaceExtensionCentre_liesOver (K := F)
        (L := sixthKummerRowField {(u:F)}) v w
      have hur : Algebra.IsUnramifiedAt (𝓞 F) Q.asIdeal :=
        sixthKummerIndividual_unramifiedAt hζ u v h6 hu Q.asIdeal hQ.over.symm
      exact (RayClass.localHigherUnitGroup_le_integralUnits v _).trans
        (adicCompletionIntegerUnits_le_chosenFinitePlaceLocalNormSubgroup v
          (chosenFinitePlaceIsUnramified_of_isUnramifiedAt v hur))
    · exact (RayClass.localHigherUnitGroup_antitone v
        (sixthKummerSharpIdeal_radical_depth_le S u v hvS hu)).trans
          (sixthKummerIndividual_principalUnit_le_chosenLocalNorm hζ (u:F) u.ne_zero v h6)

variable [NumberField.IsTotallyComplex F]

def sixthKummerSharpRayCharacter
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : sixthWildPrimes F ⊆ S) (u : Fˣ) :
    EvenIdealRayCharacter F (sixthKummerSharpIdeal S u) := by
  letI := sixthKummerRowField_isAbelianGalois hζ {(u:F)}
  exact ArtinRay.idealRayCharacter_of_localNorm _ (sixthKummerSharpIdeal_ne_zero S u)
    (sixthKummerSharpIdeal_localNorm hζ S hS u)
    (sixthKummerSharpIdeal_unramified_outside hζ S hS u)
    (sixthKummerRowCharacter hζ {(u:F)} (u:F) (Finset.mem_singleton_self _) u.ne_zero)

theorem sixthKummerSharpRayCharacter_idealHom
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : sixthWildPrimes F ⊆ S) (u : Fˣ) :
    (sixthKummerSharpRayCharacter hζ S hS u).idealHom=
      GaloisIdealCharacter.idealHom F (sixthKummerRowField {(u:F)})
        (sixthKummerRowCharacter hζ {(u:F)} (u:F) (Finset.mem_singleton_self _) u.ne_zero) := rfl

theorem sixthKummerSharpRayCharacter_isNonprincipal
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : sixthWildPrimes F ⊆ S) (u : Fˣ)
    (hpow : ¬∃ t : F, t^6=(u:F)) :
    (sixthKummerSharpRayCharacter hζ S hS u).IsNonprincipal := by
  let := sixthKummerRowField_isAbelianGalois hζ {(u:F)}
  let χ := sixthKummerRowCharacter hζ {(u:F)} (u:F) (Finset.mem_singleton_self _) u.ne_zero
  have hχ : χ ≠ 1 := fun h => hpow
    ((sixthKummerRowCharacter_one_iff_exists_sixthPower hζ {(u:F)} (u:F)
      (Finset.mem_singleton_self _) u.ne_zero).mp h)
  obtain ⟨v,hv,hvalue⟩ := ArtinRay.exists_prime_frobenius_value_ne_one
    (integralIdealRayModulus _ (sixthKummerSharpIdeal_ne_zero S u))
    (ArtinRay.integralIdeal_congruence_le_norm_of_local _ _
      (sixthKummerSharpIdeal_localNorm hζ S hS u))
    (sixthKummerSharpIdeal_unramified_outside hζ S hS u) χ hχ
  have hnd : ¬v.asIdeal ∣ sixthKummerSharpIdeal S u :=
    mt (integralIdealFiniteModulus_mem_support (sixthKummerSharpIdeal S u)
      (sixthKummerSharpIdeal_ne_zero S u) v).mpr hv
  have hnle : ¬sixthKummerSharpIdeal S u ≤ v.asIdeal :=
    fun h => hnd (Ideal.dvd_iff_le.mpr h)
  obtain ⟨a,ha,han⟩ := Set.not_subset.mp hnle
  have hcop : IsCoprime v.asIdeal (sixthKummerSharpIdeal S u) := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    exact (Ideal.isMaximal_iff.mp inferInstance).2 _ a le_sup_left han (Submodule.mem_sup_right ha)
  refine ⟨v.asIdeal,v.ne_bot,hcop,?_⟩
  rw [sixthKummerSharpRayCharacter_idealHom,GaloisIdealCharacter.idealHom_prime]
  exact hvalue

end
end ArtinMatthews
