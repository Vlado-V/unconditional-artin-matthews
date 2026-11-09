module

public import ArtinMatthews.KummerPrimitiveRowData
public import ArtinMatthews.ArtinFrobeniusGoodPrimeSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Injectivity of the actual primitive coefficient family. Equality is
tested at an Artin prime avoiding both old moduli and the common coarse
modulus; conductor divisibility also excludes both new bad-prime sets. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
variable [NumberField.IsTotallyComplex K]

omit [Algebra K ℂ] [NumberField.IsTotallyComplex K] in
theorem integralPrime_mem_rationalPrimeTo (R : ℕ) [NeZero R]
    (v : HeightOneSpectrum (𝓞 K)) (h : IsCoprime v.asIdeal (rationalModulusIdeal (𝓞 K) R)) :
    integralIdealFractionalUnit v.asIdeal v.ne_bot ∈
      RayClass.primeToModulusIdeals (rationalIdealRayModulus K R) :=
  (integralIdealPrimeToIdeal (rationalModulusIdeal (𝓞 K) R)
    (rationalModulusIdeal_ne_bot R) v.asIdeal v.ne_bot h).property

theorem boundedKummerPrimitiveDatum_prime_agreement {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : NonprincipalIdealRowIndex S N)
    (d : BoundedKummerPrimitiveDatum hζ S N i) (v : HeightOneSpectrum (𝓞 K))
    (hold : IsCoprime v.asIdeal (sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i.1)))
    (hcommon : IsCoprime v.asIdeal (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K
      (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N)))))) :
    d.character.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot)=
      boundedRowGaloisCharacter hζ S N i.1
        (GaloisIdealCharacter.primeFrobenius K
          (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))) v) := by
  let I := integralIdealPrimeToIdeal _ (sixthKummerSharpIdeal_ne_zero S _)
    v.asIdeal v.ne_bot hold
  have hI : (I:FractionalIdealGroup K) ∈ RayClass.primeToModulusIdeals (rationalIdealRayModulus K
      (discriminantDegreeModulus K
        (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))))) :=
    integralPrime_mem_rationalPrimeTo _ v hcommon
  have h := boundedKummerPrimitiveDatum_agrees_common hζ S N i d I hI
  change d.character.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot)=
    GaloisIdealCharacter.idealHom K
      (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N)))
      (boundedRowGaloisCharacter hζ S N i.1)
      (integralIdealFractionalUnit v.asIdeal v.ne_bot) at h
  rwa [GaloisIdealCharacter.idealHom_prime] at h

theorem boundedKummerPrimitiveDatum_coefficient_injective {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hClass : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (d : ∀ i : NonprincipalIdealRowIndex S N, BoundedKummerPrimitiveDatum hζ S N i) :
    Function.Injective (fun i => (d i).character.coefficient) := by
  intro i j he
  let L := sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
  let := sixthKummerRowField_isAbelianGalois hζ
    (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
  have hχ : boundedRowGaloisCharacter hζ S N i.1=boundedRowGaloisCharacter hζ S N j.1 :=
    ArtinRay.galoisCharacter_eq_of_primitive_coefficients
      (sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i.1))
      (sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N j.1))
      (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L))
      (sixthKummerSharpIdeal_ne_zero S _) (sixthKummerSharpIdeal_ne_zero S _)
      (rationalModulusIdeal_ne_bot _) (d i).character (d j).character
      (d i).old_le (d j).old_le
      (boundedRowGaloisCharacter hζ S N i.1) (boundedRowGaloisCharacter hζ S N j.1)
      (boundedKummerPrimitiveDatum_prime_agreement hζ S N i (d i))
      (boundedKummerPrimitiveDatum_prime_agreement hζ S N j (d j)) he
  exact Subtype.ext (boundedRowGaloisCharacter_injective hζ S hClass N hχ)

theorem chosenKummerPrimitiveDatum_coefficient_injective {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) :
    Function.Injective (fun i => (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character.coefficient) :=
  boundedKummerPrimitiveDatum_coefficient_injective hζ S hClass N _

def chosenKummerPrimitiveCoefficientFamily {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) :
    Finset (integralFractionalIdeals K → ℂ) :=
  Finset.univ.image (fun i => (chosenKummerPrimitiveDatum hζ S hWild hClass N i).character.coefficient)

theorem chosenKummerPrimitiveCoefficientFamily_card {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (hN : 1 ≤ N) :
    (chosenKummerPrimitiveCoefficientFamily hζ S hWild hClass N).card=
      (exteriorBoundedIdealRows S N).card*(exteriorUnitSixthRepresentatives S).card-1 := by
  rw [chosenKummerPrimitiveCoefficientFamily,Finset.card_image_of_injective _
    (chosenKummerPrimitiveDatum_coefficient_injective hζ S hWild hClass N),Finset.card_univ,
    Fintype.card_coe]
  exact nonprincipalIdealRows_card S hClass N hN

end
end ArtinMatthews
