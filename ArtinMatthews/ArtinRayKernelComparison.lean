module

public import ArtinMatthews.ArtinFrobeniusConductorSupport
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
public import ArtinMatthews.ArtinRayPrimeComparison
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.ArithmeticIdealArtin


set_option backward.privateInPublic true
@[expose] public section

/-! Actual arithmetic Artin reciprocity identifies the Mathlib Frobenius
ideal character. The principal-ray conclusion is derived from that actual
Artin map, rather than supplied as a ray-kernel hypothesis. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
noncomputable section
open scoped NumberField Classical
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
  GlobalClassFieldTheory.IdealClassFieldTheory
open GaloisIdealCharacter

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

theorem idealCharacter_eq_artin_comp
    (m : RayClass.Modulus K)
    (hm : m.congruenceSubgroup ≤ (ideleClassNorm K L).range)
    (hunram : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v ∉ m.finitePart.support →
      Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val)
    (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    (idealHom K L χ).comp (RayClass.primeToModulusIdeals m).subtype =
      χ.comp (arithmeticIdealArtinGaloisMap (K := K) (L := L) m hm) := by
  apply RayClass.primeToModulusIdeals_hom_ext m
  intro v hv
  change idealHom K L χ (FractionalIdealGroup.prime v) =
    χ (arithmeticIdealArtinGaloisMap (K := K) (L := L) m hm
      (RayClass.primeToModulusIdeal m v hv))
  rw [arithmeticIdealArtinGaloisMap_primeIdeal_eq_arithmeticFinitePlacePrimeArtin]
  change idealHom K L χ (integralIdealFractionalUnit v.asIdeal v.ne_bot) = _
  exact idealHom_prime_arithmeticArtin χ v (hunram v hv)

theorem idealCharacter_principalRay_eq_one
    (m : RayClass.Modulus K)
    (hm : m.congruenceSubgroup ≤ (ideleClassNorm K L).range)
    (hunram : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      v ∉ m.finitePart.support →
      Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).val)
    (χ : (L ≃ₐ[K] L) →* ℂˣ) (I : RayClass.primeToModulusIdeals m)
    (hI : I ∈ RayClass.principalRayIdealSubgroup m) :
    idealHom K L χ I = 1 := by
  have h := DFunLike.congr_fun (idealCharacter_eq_artin_comp m hm hunram χ) I
  change idealHom K L χ I = χ (arithmeticIdealArtinGaloisMap m hm I) at h
  have hk : arithmeticIdealArtinGaloisMap (K := K) (L := L) m hm I = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [arithmeticIdealArtinGaloisMap_ker]
    exact principalRayIdealSubgroup_le_idealArtinKernel m
      (ideleClassNorm K L).range hm hI
  rwa [hk,map_one] at h

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
