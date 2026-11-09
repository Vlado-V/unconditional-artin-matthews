module

public import ArtinMatthews.ArtinRayIdealResidueRealization
public import ArtinMatthews.ArtinRayConductor
public import ArtinMatthews.ArtinRayKernelComparison
public import ArtinMatthews.VaryingKummerAnalyticRayIdealModulus


set_option backward.privateInPublic true
@[expose] public section

/-! Actual local norm containment gives the global Artin congruence
kernel and an ideal-modulus Frobenius character. No principal-ray law is
assumed: it is proved through the genuine idele-class norm and Artin map. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open GaloisIdealCharacter
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]

theorem integralIdeal_congruence_le_norm_of_local (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hlocal : ∀ v : HeightOneSpectrum (𝓞 K),
      RayClass.localHigherUnitGroup v (integralIdealFiniteModulus M hM v) ≤
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v) :
    (integralIdealRayModulus M hM).congruenceSubgroup ≤ (ideleClassNorm K L).range := by
  have hfinite := ideleClassNormDefiningModulus_le_of_localHigherUnitGroup_le
    (K := K) (L := L) (integralIdealFiniteModulus M hM) hlocal
  have hmod : RayClass.Modulus.narrowOfFinite
      (ideleClassNormDefiningModulus (K := K) (L := L)) ≤ integralIdealRayModulus M hM := by
    constructor
    · exact hfinite
    · rw [modulus_infinitePart_eq_empty]
      exact Finset.empty_subset _
  exact (RayClass.Modulus.congruenceSubgroup_antitone hmod).trans
    (ideleClassNormDefiningModulus_isDefiningModulus (K := K) (L := L))

omit [NumberField.IsTotallyComplex K] in
theorem principalIdele_mem_idealRay_of_congruence (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (a : 𝓞 K) (ha : a ≠ 0) (hac : a-1 ∈ M) :
    IdeleGroup.principalIdele K (Units.mk0 (a:K) (by exact_mod_cast ha)) ∈
      RayClass.idelePrimeToModulusSubgroup (integralIdealRayModulus M hM) := by
  constructor
  · change _ ∈ (integralIdealRayModulus M hM).infiniteCongruenceSubgroup
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    intro v hv
    simp only [integralIdealRayModulus,RayClass.Modulus.infinitePart_ofFinite,Finset.notMem_empty] at hv
  · intro v hv
    apply principal_local_mem_higherUnits v
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)) a ha
    have hc := (integralIdeal_mem_iff_modulus_prime_powers M hM (a-1)).mp hac v hv
    have hh := (completed_integral_mem_prime_pow_iff v _ (a-1)).mpr hc
    simpa only [map_sub,map_one,integralIdealRayModulus,RayClass.Modulus.finitePart_ofFinite] using hh

theorem idealCharacter_idealKernel_of_localNorm (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hlocal : ∀ v : HeightOneSpectrum (𝓞 K),
      RayClass.localHigherUnitGroup v (integralIdealFiniteModulus M hM v) ≤
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v)
    (hur : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∉ (integralIdealFiniteModulus M hM).support →
      Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val)
    (χ : Gal(L/K) →* ℂˣ) : PrincipalIdealRay.KernelLaw (idealHom K L χ) M := by
  intro a ha hac
  let x : Kˣ := Units.mk0 (a:K) (by exact_mod_cast ha)
  let y : RayClass.idelePrimeToModulusSubgroup (integralIdealRayModulus M hM) :=
    ⟨IdeleGroup.principalIdele K x,principalIdele_mem_idealRay_of_congruence M hM a ha hac⟩
  let I := RayClass.primeToIdealMap (integralIdealRayModulus M hM) y
  have hI : I ∈ RayClass.principalRayIdealSubgroup (integralIdealRayModulus M hM) :=
    ⟨y,⟨x,rfl⟩,rfl⟩
  have H := idealCharacter_principalRay_eq_one (integralIdealRayModulus M hM)
    (integralIdeal_congruence_le_norm_of_local M hM hlocal) hur χ I hI
  have he : (I:FractionalIdealGroup K)=integralIdealFractionalUnit (Ideal.span {a})
      (by simpa only [ne_eq,Ideal.span_singleton_eq_bot] using ha) := by
    change IdeleGroup.fractionalIdeal (IdeleGroup.principalIdele K x)=_
    rw [IdeleGroup.fractionalIdeal_principalIdele]
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact (FractionalIdeal.coeIdeal_span_singleton a).symm
  change idealHom K L χ (I:FractionalIdealGroup K)=1 at H
  change idealHom K L χ (integralIdealFractionalUnit (Ideal.span {a}) _)=1
  rwa [he] at H

def idealRayCharacter_of_localNorm (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hlocal : ∀ v : HeightOneSpectrum (𝓞 K),
      RayClass.localHigherUnitGroup v (integralIdealFiniteModulus M hM v) ≤
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v)
    (hur : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∉ (integralIdealFiniteModulus M hM).support →
      Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val)
    (χ : Gal(L/K) →* ℂˣ) : EvenIdealRayCharacter K M :=
  PrincipalIdealRay.realize (idealHom K L χ) M hM
    (idealCharacter_idealKernel_of_localNorm M hM hlocal hur χ) (idealHom_finiteOrder K L χ)

@[simp] theorem idealRayCharacter_of_localNorm_idealHom (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (hlocal : ∀ v : HeightOneSpectrum (𝓞 K),
      RayClass.localHigherUnitGroup v (integralIdealFiniteModulus M hM v) ≤
        chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v)
    (hur : ∀ v : HeightOneSpectrum (𝓞 K),
      v ∉ (integralIdealFiniteModulus M hM).support →
      Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val)
    (χ : Gal(L/K) →* ℂˣ) :
    (idealRayCharacter_of_localNorm M hM hlocal hur χ).idealHom=idealHom K L χ := rfl

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
