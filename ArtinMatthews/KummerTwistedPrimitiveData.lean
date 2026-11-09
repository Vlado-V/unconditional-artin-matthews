module

public import ArtinMatthews.IdealRayCharacterProduct
public import ArtinMatthews.KummerPrimitiveRowData


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive presentations of the actual fixed-character twists
`η * χ_u⁻¹`. The conductor cost is the norm of the fixed modulus times
the sharp Kummer cost. Principality is not assumed away. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
variable [NumberField.IsTotallyComplex K]

def twistedKummerOldModulus (M : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    Ideal (𝓞 K) := M * sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i)

omit [Algebra K ℂ] [NumberField.IsTotallyComplex K] in
theorem twistedKummerOldModulus_ne_zero {M : Ideal (𝓞 K)} (hM : M ≠ ⊥)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    twistedKummerOldModulus M S N i ≠ ⊥ :=
  mul_ne_zero hM (sixthKummerSharpIdeal_ne_zero S _)

structure BoundedKummerTwistedPrimitiveDatum {M : Ideal (𝓞 K)}
    (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) (i : ExteriorIdealRowIndex S N) where
  modulus : IdealConductorModulus K
  character : EvenIdealRayCharacter K modulus.val
  primitive : IsPrimitiveOnIdeals character.residue
  old_le : twistedKummerOldModulus M S N i ≤ modulus.val
  norm_le : modulus.val.absNorm ≤ M.absNorm * (sixthKummerFixedIdeal S).absNorm * N
  agrees : ∀ I : RayClass.primeToModulusIdeals (integralIdealRayModulus
      (twistedKummerOldModulus M S N i) (twistedKummerOldModulus_ne_zero hM S N i)),
    character.idealHom (I : FractionalIdealGroup K) = η.idealHom (I : FractionalIdealGroup K) *
      (GaloisIdealCharacter.idealHom K
        (sixthKummerRowField {(exteriorBoundedIdealRowUnit S N i : K)})
        (sixthKummerRowCharacter hζ {(exteriorBoundedIdealRowUnit S N i : K)}
          (exteriorBoundedIdealRowUnit S N i : K) (Finset.mem_singleton_self _)
          (Units.ne_zero _)) (I : FractionalIdealGroup K))⁻¹

theorem boundedKummerTwistedPrimitiveDatum_nonempty {M : Ideal (𝓞 K)}
    (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    Nonempty (BoundedKummerTwistedPrimitiveDatum η hM hζ S N i) := by
  let χ := η.twistInverseAtProduct
    (sixthKummerSharpRayCharacter hζ S hWild (exteriorBoundedIdealRowUnit S N i))
    hM (sixthKummerSharpIdeal_ne_zero S _)
  obtain ⟨f,hf,hMf,Ψ,hprim,hnorm,_hmask,hagree⟩ :=
    χ.exists_primitive_idealCharacter (twistedKummerOldModulus_ne_zero hM S N i)
  refine ⟨⟨⟨f,hf⟩,Ψ,hprim,hMf,hnorm.trans ?_,?_⟩⟩
  · change (M * sixthKummerSharpIdeal S (exteriorBoundedIdealRowUnit S N i)).absNorm ≤ _
    rw [map_mul,sixthKummerSharpIdeal_absNorm,← mul_assoc]
    exact Nat.mul_le_mul_left _ (exteriorBoundedIdealRow_radical_norm_le S hClass N i)
  · intro I
    exact hagree I

def chosenKummerTwistedPrimitiveDatum {M : Ideal (𝓞 K)}
    (η : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) {ζ : K} (hζ : IsPrimitiveRoot ζ 6)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hWild : sixthWildPrimes K ⊆ S)
    (hClass : exteriorPrincipalizingPrimes K ⊆ S) (N : ℕ) (i : ExteriorIdealRowIndex S N) :
    BoundedKummerTwistedPrimitiveDatum η hM hζ S N i :=
  Classical.choice (boundedKummerTwistedPrimitiveDatum_nonempty η hM hζ S hWild hClass N i)

end
end ArtinMatthews
