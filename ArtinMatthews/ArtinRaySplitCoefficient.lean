module

public import ArtinMatthews.ArtinRayFaithfulEulerLocal
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces


set_option backward.privateInPublic true
@[expose] public section

/-! Complete local splitting gives the literal coefficient one for the
actual global norm-conductor ray character. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField Classical
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

theorem arithmeticFinitePlacePrimeArtin_eq_one_of_splitsCompletely
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit : FinitePlaceSplitsCompletely (K := K) (L := L) v) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v = 1 := by
  have hnorm := chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely v hsplit
  have hlocal : Reciprocity.chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
      (FiniteIdeleGroup.chosenLocalOrderSection v 1) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [Reciprocity.chosenFinitePlaceArtinMonoidHom_ker, hnorm]
    exact Subgroup.mem_top _
  rw [arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin,
    Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply, hlocal, inv_one]

variable [IsTotallyComplex K]

theorem abelianNormConductorRayCharacter_prime_of_splitsCompletely
    (χ : Gal(L/K) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (hsplit : FinitePlaceSplitsCompletely (K := K) (L := L) v) :
    (abelianNormConductorRayCharacter K L χ).allCoefficient v.asIdeal = 1 := by
  have hv : v ∉ (integralIdealFiniteModulus (abelianNormConductorIdeal K L)
      (abelianNormConductorIdeal_ne_bot K L)).support := by
    rw [abelianNormConductorIdeal_modulus]
    exact not_mem_ideleClassNorm_narrowFiniteConductor_support_of_splitsCompletely v hsplit
  have hunram := abelianNormConductorIdeal_unramified K L v hv
  have hc : IsCoprime v.asIdeal (abelianNormConductorIdeal K L) := by
    rw [abelianNormConductor_prime_coprime_iff_unramified v
      (GaloisIdealCharacter.primeAbove K L v)]
    exact hunram
  rw [EvenIdealRayCharacter.allCoefficient, dite_eq_left v.ne_bot, ite_eq_left hc,
    abelianNormConductorRayCharacter_idealHom, idealHom_prime_arithmeticArtin χ v hunram,
    arithmeticFinitePlacePrimeArtin_eq_one_of_splitsCompletely v hsplit, map_one,
    Units.val_one]

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
