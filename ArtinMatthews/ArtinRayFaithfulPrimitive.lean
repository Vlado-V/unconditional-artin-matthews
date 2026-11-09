module

public import ArtinMatthews.ArtinRayNormConductor
public import ArtinMatthews.IdealRayPrimitivePresentation


set_option backward.privateInPublic true
@[expose] public section

/-! A faithful character of the actual abelian Galois group realizes
the exact norm conductor. A residue descent would make the smaller
modulus defining for the genuine global norm subgroup. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain RayClass
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open GlobalClassFieldTheory.IdealClassFieldTheory
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]

private theorem rayClass_primeToRepresentative (m : Modulus K) (x : IdeleClassGroup K) :
    ∃ a : idelePrimeToModulusSubgroup m,
      QuotientGroup.mk' m.congruenceSubgroup
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) (a : IdeleGroup K)) =
      QuotientGroup.mk' m.congruenceSubgroup x := by
  let e := rayClassGroupEquivIdealRayClassGroup m
  obtain ⟨I, hI⟩ := QuotientGroup.mk'_surjective (principalRayIdealSubgroup m)
    (e (QuotientGroup.mk' m.congruenceSubgroup x))
  obtain ⟨a, rfl⟩ := primeToIdealMap_surjective m I
  refine ⟨a, e.injective ?_⟩
  rw [rayClassGroupEquivIdealRayClassGroup_mk_primeTo]
  exact hI

variable {L : Type} [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsAbelianGalois K L] [NumberField.IsTotallyComplex K]

private theorem residueDescent_defining
    (χ : Gal(L/K) →* ℂˣ) (hχ : Function.Injective χ)
    (f : Ideal (𝓞 K)) (hf : f ≠ ⊥) (hMf : abelianNormConductorIdeal K L ≤ f)
    (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, (abelianNormConductorRayCharacter K L χ).residue
      (Ideal.Quotient.mk (abelianNormConductorIdeal K L) a) =
      if IsUnit (Ideal.Quotient.mk (abelianNormConductorIdeal K L) a)
        then φ (Ideal.Quotient.mk f a) else 0) :
    (integralIdealRayModulus f hf).congruenceSubgroup ≤ (ideleClassNorm K L).range := by
  let M := abelianNormConductorIdeal K L
  let hM := abelianNormConductorIdeal_ne_bot K L
  let ψ := abelianNormConductorRayCharacter K L χ
  let m := integralIdealRayModulus M hM
  let n := integralIdealRayModulus f hf
  have hnm : n ≤ m := integralIdealRayModulus_antitone hM hf hMf
  have hmn := Modulus.congruenceSubgroup_antitone hnm
  have hm : m.congruenceSubgroup ≤ (ideleClassNorm K L).range :=
    integralIdeal_congruence_le_norm_of_local M hM (abelianNormConductorIdeal_localNorm K L)
  intro x hx
  obtain ⟨a, ha⟩ := rayClass_primeToRepresentative m x
  let y : IdeleClassGroup K := QuotientGroup.mk' (IdeleGroup.principalSubgroup K) (a : IdeleGroup K)
  let p := QuotientGroup.map m.congruenceSubgroup n.congruenceSubgroup
    (MonoidHom.id (IdeleClassGroup K)) (fun _ h => hmn h)
  have hny := congrArg p ha
  change QuotientGroup.mk' n.congruenceSubgroup y = QuotientGroup.mk' n.congruenceSubgroup x at hny
  have hx1 : QuotientGroup.mk' n.congruenceSubgroup x = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hx
  let a' := primeToIdeleConductorInclusion hnm a
  have hsmall : idealRayProjection n a' = 1 := by
    rw [← rayClassGroupEquivIdealRayClassGroup_mk_primeTo]
    change rayClassGroupEquivIdealRayClassGroup n (QuotientGroup.mk' n.congruenceSubgroup y) = 1
    rw [hny, hx1, map_one]
  have hproj : EvenIdealRayCharacter.conductorIdealProjection hM f hf hMf (idealRayProjection m a) = 1 :=
    (idealConductorProjection_idele hnm a).trans hsmall
  have hval := ψ.rayClassCharacter_conductor_kernel hM f hf hMf φ hmask
    (MonoidHom.mem_ker.mpr hproj)
  change ψ.rayClassCharacter hM (idealRayProjection m a) = 1 at hval
  have hI : ψ.idealHom (primeToIdealMap m a : FractionalIdealGroup K) = 1 := hval
  rw [abelianNormConductorRayCharacter_idealHom] at hI
  have hArtin := DFunLike.congr_fun
    (idealCharacter_eq_artin_comp m hm (abelianNormConductorIdeal_unramified K L) χ)
    (primeToIdealMap m a)
  change GaloisIdealCharacter.idealHom K L χ (primeToIdealMap m a : FractionalIdealGroup K) =
    χ (arithmeticIdealArtinGaloisMap m hm (primeToIdealMap m a)) at hArtin
  rw [hI, arithmeticIdealArtinGaloisMap_apply, GlobalClassFields.idealArtinMap_primeToIdealMap] at hArtin
  have hy : Reciprocity.arithmeticGlobalNormResidueMonoidHom K L y = 1 :=
    hχ (hArtin.symm.trans (map_one χ).symm)
  have hyNorm : y ∈ (ideleClassNorm K L).range := by
    rw [← Reciprocity.arithmeticGlobalNormResidueMonoidHom_ker]
    exact MonoidHom.mem_ker.mpr hy
  have hyx : y / x ∈ m.congruenceSubgroup := (QuotientGroup.eq_iff_div_mem).mp ha
  have hdiv : y / x = y * x⁻¹ := div_eq_mul_inv y x
  have hmul : y * x⁻¹ ∈ (ideleClassNorm K L).range := hdiv ▸ hm hyx
  have hxinv : x⁻¹ ∈ (ideleClassNorm K L).range :=
    ((ideleClassNorm K L).range.mul_mem_cancel_left hyNorm).mp hmul
  exact (ideleClassNorm K L).range.inv_mem_iff.mp hxinv

theorem abelianNormConductorRayCharacter_primitive
    (χ : Gal(L/K) →* ℂˣ) (hχ : Function.Injective χ) :
    IsPrimitiveOnIdeals (abelianNormConductorRayCharacter K L χ).residue := by
  let M := abelianNormConductorIdeal K L
  let hM := abelianNormConductorIdeal_ne_bot K L
  let ψ := abelianNormConductorRayCharacter K L χ
  obtain ⟨f, hf, hMf, φ, _, hprim, _, hmask, _, _, _, _⟩ :=
    ψ.exists_primitive_idealRay_presentation hM
  have hdef := residueDescent_defining χ hχ f hf hMf φ hmask
  have hle := (ideleClassNormConductorialSubgroup (K := K) (L := L)).narrowFiniteConductor_le hdef
  change ideleClassNormNarrowFiniteConductor (K := K) (L := L) ≤ integralIdealFiniteModulus f hf at hle
  rw [← abelianNormConductorIdeal_modulus K L] at hle
  have heq : f = M := le_antisymm (integralIdeal_le_of_finiteModulus_le hM hf hle) hMf
  subst f
  have hresidue : ψ.residue = φ := by
    apply MulChar.ext'
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    by_cases ha : IsUnit (Ideal.Quotient.mk M a)
    · exact (hmask a).trans (ite_eq_left ha)
    · exact ((hmask a).trans (ite_eq_right ha)).trans (MulChar.map_nonunit _ ha).symm
  change IsPrimitiveOnIdeals ψ.residue
  rwa [hresidue]

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
