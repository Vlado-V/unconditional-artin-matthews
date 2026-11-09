module

public import ArtinMatthews.KummerTwistedPrimitiveData
public import ArtinMatthews.KummerPrimitiveRowInjectivity
public import ArtinMatthews.ArtinFrobeniusTwistedSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Literal fixed-character Kummer twists remain distinct after primitive
descent. All comparisons use primes avoiding both old product moduli and
the common realization modulus. There is at most one principal twist. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
variable [NumberField.IsTotallyComplex K]

theorem boundedKummerTwistedPrimitiveDatum_prime_agreement {M : Ideal (𝓞 K)}
    (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : ExteriorIdealRowIndex S N)
    (d : BoundedKummerTwistedPrimitiveDatum η hM hζ S N i)
    (v : HeightOneSpectrum (𝓞 K))
    (hold : IsCoprime v.asIdeal (twistedKummerOldModulus M S N i))
    (hcommon : IsCoprime v.asIdeal (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K
      (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N)))))) :
    d.character.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) =
      η.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) *
        (boundedRowGaloisCharacter hζ S N i (GaloisIdealCharacter.primeFrobenius K
          (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))) v))⁻¹ := by
  let I := integralIdealPrimeToIdeal _ (twistedKummerOldModulus_ne_zero hM S N i)
    v.asIdeal v.ne_bot hold
  have hI := integralPrime_mem_rationalPrimeTo _ v hcommon
  have h := sixthKummerRow_rayIdealHom_eq_individual hζ
    (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
    (exteriorBoundedIdealRowUnit S N i : K)
    (by simpa only [sixthUnitRowParameters] using
      (Finset.mem_image_of_mem (fun u : Kˣ => (u : K)) (exteriorBoundedIdealRowUnit_mem S N i)))
    (Units.ne_zero _) ⟨integralIdealFractionalUnit v.asIdeal v.ne_bot,hI⟩
  change GaloisIdealCharacter.idealHom K
    (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N)))
    (boundedRowGaloisCharacter hζ S N i) (integralIdealFractionalUnit v.asIdeal v.ne_bot) = _ at h
  rw [GaloisIdealCharacter.idealHom_prime] at h
  exact (d.agrees I).trans (congrArg (fun z =>
    η.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot) * z⁻¹) h.symm)

theorem boundedKummerTwistedPrimitiveDatum_coefficient_injective {M : Ideal (𝓞 K)}
    (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hClass : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (d : ∀ i, BoundedKummerTwistedPrimitiveDatum η hM hζ S N i) :
    Function.Injective (fun i => (d i).character.coefficient) := by
  intro i j he
  let L := sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
  let := sixthKummerRowField_isAbelianGalois hζ
    (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
  apply boundedRowGaloisCharacter_injective hζ S hClass N
  exact ArtinRay.galoisCharacter_eq_of_twisted_coefficients
    (twistedKummerOldModulus M S N i) (twistedKummerOldModulus M S N j)
    (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L))
    (twistedKummerOldModulus_ne_zero hM S N i) (twistedKummerOldModulus_ne_zero hM S N j)
    (rationalModulusIdeal_ne_bot _) (d i).character (d j).character (d i).old_le (d j).old_le
    η.idealHom (boundedRowGaloisCharacter hζ S N i) (boundedRowGaloisCharacter hζ S N j)
    (boundedKummerTwistedPrimitiveDatum_prime_agreement η hM hζ S N i (d i))
    (boundedKummerTwistedPrimitiveDatum_prime_agreement η hM hζ S N j (d j)) he

theorem boundedKummerTwistedPrimitiveDatum_principal_unique {M : Ideal (𝓞 K)}
    (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hClass : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (d : ∀ i, BoundedKummerTwistedPrimitiveDatum η hM hζ S N i)
    (i j : ExteriorIdealRowIndex S N)
    (hi : ¬(d i).character.IsNonprincipal) (hj : ¬(d j).character.IsNonprincipal) : i = j := by
  let L := sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
  let := sixthKummerRowField_isAbelianGalois hζ
    (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
  apply boundedRowGaloisCharacter_injective hζ S hClass N
  exact ArtinRay.galoisCharacter_eq_of_principal_twists
    (twistedKummerOldModulus M S N i) (twistedKummerOldModulus M S N j)
    (rationalModulusIdeal (𝓞 K) (discriminantDegreeModulus K L))
    (twistedKummerOldModulus_ne_zero hM S N i) (twistedKummerOldModulus_ne_zero hM S N j)
    (rationalModulusIdeal_ne_bot _) (d i).character (d j).character (d i).old_le (d j).old_le
    η.idealHom (boundedRowGaloisCharacter hζ S N i) (boundedRowGaloisCharacter hζ S N j)
    (boundedKummerTwistedPrimitiveDatum_prime_agreement η hM hζ S N i (d i))
    (boundedKummerTwistedPrimitiveDatum_prime_agreement η hM hζ S N j (d j)) hi hj

theorem boundedKummerTwistedPrimitiveDatum_principal_count {M : Ideal (𝓞 K)}
    (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hClass : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) (d : ∀ i, BoundedKummerTwistedPrimitiveDatum η hM hζ S N i) :
    (Finset.univ.filter (fun i => ¬(d i).character.IsNonprincipal)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact boundedKummerTwistedPrimitiveDatum_principal_unique η hM hζ S hClass N d i j
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

end
end ArtinMatthews
