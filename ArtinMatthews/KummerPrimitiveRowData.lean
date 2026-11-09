module

public import ArtinMatthews.KummerNonprincipalRows
public import ArtinMatthews.SixthKummerSharpRows
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleConductorSieve


set_option backward.privateInPublic true
@[expose] public section

/-! Actual primitive nonprincipal characters chosen for the literal
bounded rows. Every field stores a proved property of this construction;
coefficient injectivity is deliberately proved in a separate leaf. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
variable [NumberField.IsTotallyComplex K]

structure BoundedKummerPrimitiveDatum {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : NonprincipalIdealRowIndex S N) where
  modulus : IdealConductorModulus K
  character : EvenIdealRayCharacter K modulus.val
  primitive : IsPrimitiveOnIdeals character.residue
  nonprincipal : character.IsNonprincipal
  old_le : sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i.1) ≤ modulus.val
  norm_le : modulus.val.absNorm ≤ (sixthKummerFixedIdeal S).absNorm*N
  agrees : ∀ I : RayClass.primeToModulusIdeals (integralIdealRayModulus
      (sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i.1))
      (sixthKummerSharpIdeal_ne_zero S _)),
    character.idealHom (I:FractionalIdealGroup K)=GaloisIdealCharacter.idealHom K
      (sixthKummerRowField {(exteriorBoundedIdealRowUnit S N i.1:K)})
      (sixthKummerRowCharacter hζ {(exteriorBoundedIdealRowUnit S N i.1:K)}
        (exteriorBoundedIdealRowUnit S N i.1:K) (Finset.mem_singleton_self _) (Units.ne_zero _))
      (I:FractionalIdealGroup K)

theorem boundedKummerPrimitiveDatum_nonempty {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : NonprincipalIdealRowIndex S N) :
    Nonempty (BoundedKummerPrimitiveDatum hζ S N i) := by
  obtain ⟨f,hf,hold,ψ,hprim,hnp,hnorm,hagree,_hmask⟩ :=
    exists_boundedIdealRow_nonprincipal_conductor hζ S hWild hClass N i.1
      (nonprincipalIdealRow_not_sixthPower S N i)
  exact ⟨⟨⟨f,hf⟩,ψ,hprim,hnp,hold,hnorm,hagree⟩⟩

def chosenKummerPrimitiveDatum {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : NonprincipalIdealRowIndex S N) :
    BoundedKummerPrimitiveDatum hζ S N i :=
  Classical.choice (boundedKummerPrimitiveDatum_nonempty hζ S hWild hClass N i)

def boundedRowGaloisCharacter {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    Gal(sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))/K) →* ℂˣ :=
  sixthKummerRowCharacter hζ (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
    (exteriorBoundedIdealRowUnit S N i:K)
    (by simpa only [sixthUnitRowParameters] using
      (Finset.mem_image_of_mem (fun u : Kˣ => (u:K)) (exteriorBoundedIdealRowUnit_mem S N i)))
    (Units.ne_zero _)

theorem boundedRowGaloisCharacter_injective {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hClass : exteriorPrincipalizingPrimes K ⊆ S)
    (N : ℕ) : Function.Injective (boundedRowGaloisCharacter hζ S N) := by
  intro i j h
  let := sixthKummerRowField_isAbelianGalois hζ
    (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
  apply exteriorBoundedIdealRowRayCharacter_coefficient_injective hζ S hClass N
  exact congrArg (fun χ => (ArtinRay.discriminantDegreeRayCharacter χ).coefficient) h

theorem boundedRowGaloisCharacter_idealHom {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    (exteriorBoundedIdealRowRayCharacter hζ S N i).idealHom=
      GaloisIdealCharacter.idealHom K
        (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N)))
        (boundedRowGaloisCharacter hζ S N i) := rfl

theorem boundedKummerPrimitiveDatum_agrees_common {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : NonprincipalIdealRowIndex S N)
    (d : BoundedKummerPrimitiveDatum hζ S N i)
    (I : RayClass.primeToModulusIdeals (integralIdealRayModulus
      (sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i.1))
      (sixthKummerSharpIdeal_ne_zero S _)))
    (hI : (I:FractionalIdealGroup K) ∈ RayClass.primeToModulusIdeals (rationalIdealRayModulus K
      (discriminantDegreeModulus K
        (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N)))))) :
    d.character.idealHom (I:FractionalIdealGroup K)=GaloisIdealCharacter.idealHom K
      (sixthKummerRowField (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N)))
      (boundedRowGaloisCharacter hζ S N i.1) (I:FractionalIdealGroup K) := by
  have h := sixthKummer_primitive_common_ideal_value hζ S (exteriorBoundedIdealRowUnit S N i.1)
    (sixthUnitRowParameters (exteriorBoundedIdealRowUnits S N))
    (by simpa only [sixthUnitRowParameters] using
      (Finset.mem_image_of_mem (fun u : Kˣ => (u:K)) (exteriorBoundedIdealRowUnit_mem S N i.1)))
    d.character d.agrees I hI
  exact h

end
end ArtinMatthews
