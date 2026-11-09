module

public import ArtinMatthews.SourceFrequencyExponents
public import ArtinMatthews.SourceGeneratorPrefix
public import ArtinMatthews.SourceExponentFiniteFNorm
public import ArtinMatthews.SourceFiniteNormalizedF


set_option backward.privateInPublic true
@[expose] public section

/-! Instantiate the genuine finite CRT normalization on the actual
prime-exponent data. All frequency orders and unit cofactors are derived. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open SourceCRTNormalization SIntegerFourier
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

def sourceFrequencyCofactor (u : sourceRing F S₀) (hu : u ≠ 0)
    (r : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) : sourceRing F S₀ :=
  (source_exact_order_factor (sourceHilbertSeed F S₀) P.val
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (sourceElementExponents F S₀ u hu P + 6 * r P)
    (u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6)
    (sourceFrequency_exact_order F S₀ hζ u hu r P).1
    (sourceFrequency_exact_order F S₀ hζ u hu r P).2).choose

theorem sourceFrequencyCofactor_spec (u : sourceRing F S₀) (hu : u ≠ 0)
    (r : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) :
    u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6 =
        sourceAllowedPrimeGenerator F hζ S₀ P ^
          (sourceElementExponents F S₀ u hu P + 6 * r P) * sourceFrequencyCofactor F S₀ hζ u hu r P ∧
      sourceFrequencyCofactor F S₀ hζ u hu r P ∉
        P.val.asIdeal.map (algebraMap (𝓞 F) (sourceRing F S₀)) :=
  (source_exact_order_factor (sourceHilbertSeed F S₀) P.val
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (sourceElementExponents F S₀ u hu P + 6 * r P)
    (u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6)
    (sourceFrequency_exact_order F S₀ hζ u hu r P).1
    (sourceFrequency_exact_order F S₀ hζ u hu r P).2).choose_spec

def sourceExponentCRTUnitFactor
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (s A r : SourcePrimeExponents F S₀) (u : sourceRing F S₀) (hu : u ≠ 0)
    (T : Finset (SourceExteriorPrime F S₀)) (i : T) : ℂ :=
  sourceFamilyUnitFactor (sourceHilbertSeed F S₀) (fun P : T => P.val.val)
    (by intro P Q h he; exact h (Subtype.ext (Subtype.ext he)))
    (fun P => P.val.property) (fun P => sourceAllowedPrimeGenerator F hζ S₀ P.val)
    (fun P => sourceAllowedPrimeGenerator_ideal F hζ S₀ P.val) (fun P => χ P.val)
    (fun P => s P.val) (fun P => A P.val) (fun P => sourceFrequencyCofactor F S₀ hζ u hu r P.val)
    (fun P => (sourceFrequencyCofactor_spec F S₀ hζ u hu r P.val).2) i

theorem sourceExponentFiniteF_normalized
    (χ : ∀ P : SourceExteriorPrime F S₀, MulChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ)
    (s A r : SourcePrimeExponents F S₀) (u : sourceRing F S₀) (hu : u ≠ 0)
    (T : Finset (SourceExteriorPrime F S₀)) (hs : s.support ⊆ T) (hA : A.support ⊆ T) :
    sourceExponentFiniteF F hζ S₀ χ s A
        (u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6) =
      ∏ P : T, sourceExponentCRTUnitFactor F S₀ hζ χ s A r u hu T P *
        standardLocalCoefficient (sourceHilbertSeed F S₀) P.val.val P.val.property
          (sourceAllowedPrimeGenerator F hζ S₀ P.val) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P.val)
          (χ P.val) (A P.val) (s P.val) (sourceElementExponents F S₀ u hu P.val + 6 * r P.val) := by
  let P : T → HeightOneSpectrum (𝓞 F) := fun i => i.val.val
  have hP : Pairwise fun i j => P i ≠ P j := by
    intro i j hij he
    exact hij (Subtype.ext (Subtype.ext he))
  have hS : ∀ i : T, P i ∉ principalizingSet (sourceHilbertSeed F S₀) := fun i => i.val.property
  let a : T → PrincipalIntegerRing (sourceHilbertSeed F S₀) :=
    fun i => sourceAllowedPrimeGenerator F hζ S₀ i.val
  have ha : ∀ i, (P i).asIdeal.map
      (algebraMap (𝓞 F) (PrincipalIntegerRing (sourceHilbertSeed F S₀))) = Ideal.span {a i} :=
    fun i => sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val
  have hwS : sourcePrimeExponentWeight F hζ S₀ χ s =
      sourceSexticWeight (sourceHilbertSeed F S₀) P hS a ha (fun i => χ i.val) (fun i => s i.val) :=
    funext (fun x => sourcePrimeExponentWeight_eq_sourceSexticWeight F hζ S₀ χ s x T hs)
  have hwA : sourcePrimeExponentWeight F hζ S₀ χ A =
      sourceSexticWeight (sourceHilbertSeed F S₀) P hS a ha (fun i => χ i.val) (fun i => A i.val) :=
    funext (fun x => sourcePrimeExponentWeight_eq_sourceSexticWeight F hζ S₀ χ A x T hA)
  have he := sourceSexticFiniteF_normalized (sourceHilbertSeed F S₀) P hP hS a ha
    (fun i => χ i.val) (fun i => s i.val) (fun i => A i.val)
    (fun i => sourceElementExponents F S₀ u hu i.val + 6 * r i.val)
    (u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6)
    (fun i => sourceFrequencyCofactor F S₀ hζ u hu r i.val)
    (fun i => (sourceFrequencyCofactor_spec F S₀ hζ u hu r i.val).1)
    (fun i => (sourceFrequencyCofactor_spec F S₀ hζ u hu r i.val).2)
  unfold sourceExponentFiniteF
  rw [sourcePrimeExponentGenerator_prefix F hζ S₀ s T hs,
    sourcePrimeExponentGenerator_prefix F hζ S₀ A T hA, hwS, hwA]
  exact he

end
end ArtinMatthews
