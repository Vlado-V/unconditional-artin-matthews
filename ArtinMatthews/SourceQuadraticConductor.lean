module

public import ArtinMatthews.SourceQuadraticPrimeFrobenius
public import ArtinMatthews.QuadraticKummerRamification
public import ArtinMatthews.ArtinRayNormConductor
public import ArtinMatthews.SourceFrequencyUnitPart
public import ArtinMatthews.SixthKummerLocalNorm
public import ArtinMatthews.SixthKummerSharpModulus


set_option backward.privateInPublic true
@[expose] public section

/-! The actual quadratic field and its primitive ray character. Its
finite conductor is the genuine abelian norm conductor. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields AngularLambda
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

abbrev SourceQuadraticField (e : E) :=
  letI : Algebra F ℂ := sourceComplexAlgebra hζ
  QuadraticKummerField (sourcePrimeExponentUnit F hζ S₀ e)

instance sourceQuadraticFieldAlgebra (e : E) : Algebra F (SourceQuadraticField F S₀ hζ e) := by
  letI : Algebra F ℂ := sourceComplexAlgebra hζ
  change Algebra F (QuadraticKummerField (sourcePrimeExponentUnit F hζ S₀ e))
  infer_instance

instance sourceQuadraticFieldFiniteDimensional (e : E) :
    FiniteDimensional F (SourceQuadraticField F S₀ hζ e) := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  change FiniteDimensional F (QuadraticKummerField (sourcePrimeExponentUnit F hζ S₀ e))
  infer_instance

instance sourceQuadraticFieldIsGalois (e : E) : IsGalois F (SourceQuadraticField F S₀ hζ e) := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  change IsGalois F (QuadraticKummerField (sourcePrimeExponentUnit F hζ S₀ e))
  infer_instance

def sourceQuadraticGaloisCharacter (e : E) : Gal(SourceQuadraticField F S₀ hζ e/F) →* ℂˣ := by
  letI : Algebra F ℂ := sourceComplexAlgebra hζ
  exact quadraticKummerCharacter (sourcePrimitiveRootSix F hζ) (sourcePrimeExponentUnit F hζ S₀ e)

theorem sourceQuadraticField_isAbelianGalois (e : E) :
    IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  exact sixthKummerRowField_isAbelianGalois (sourcePrimitiveRootSix F hζ) _

local instance quadraticAbelian (e : E) : IsAbelianGalois F (SourceQuadraticField F S₀ hζ e) :=
  sourceQuadraticField_isAbelianGalois F S₀ hζ e

def sourceQuadraticConductor (e : E) : Ideal (𝓞 F) :=
  ArtinRay.abelianNormConductorIdeal F (SourceQuadraticField F S₀ hζ e)

theorem sourceQuadraticConductor_ne_bot (e : E) : sourceQuadraticConductor F S₀ hζ e ≠ ⊥ :=
  ArtinRay.abelianNormConductorIdeal_ne_bot F _

theorem sourceQuadraticConductor_exterior_le_one (e : E) (P : SourceExteriorPrime F S₀) :
    integralIdealFiniteModulus (sourceQuadraticConductor F S₀ hζ e)
      (sourceQuadraticConductor_ne_bot F S₀ hζ e) P.val ≤ 1 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  change integralIdealFiniteModulus
    (ArtinRay.abelianNormConductorIdeal F (SourceQuadraticField F S₀ hζ e))
    (ArtinRay.abelianNormConductorIdeal_ne_bot F _) _ ≤ _
  rw [ArtinRay.abelianNormConductorIdeal_modulus,
    ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus, ideleClassNormDefiningModulus_apply]
  exact ideleClassNormLocalHigherUnitExponent_min P.val
    (sixthKummerIndividual_principalUnit_le_chosenLocalNorm (sourcePrimitiveRootSix F hζ)
      ((sourcePrimeExponentUnit F hζ S₀ e : F) ^ 3)
      (pow_ne_zero _ (sourcePrimeExponentUnit F hζ S₀ e).ne_zero) P.val
      (source_exterior_six_not_mem F S₀ P.val P.property))

theorem sourceQuadraticConductor_exterior_zero (e : E) (P : SourceExteriorPrime F S₀)
    (hP : e P = 0) :
    integralIdealFiniteModulus (sourceQuadraticConductor F S₀ hζ e)
      (sourceQuadraticConductor_ne_bot F S₀ hζ e) P.val = 0 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let u := sourcePrimeExponentUnit F hζ S₀ e
  have hu : exteriorPrincipalValuation P.val (u ^ 3) = 0 := by
    rw [exteriorPrincipalValuation_pow, sourceExteriorPrincipalValuation_eq_neg_log,
      sourcePrimeExponentUnit_val, sourcePrimeExponentGenerator_valuation, hP,
      Nat.cast_zero, neg_zero, WithZero.exp_zero, WithZero.log_one, neg_zero, mul_zero]
  change integralIdealFiniteModulus
    (ArtinRay.abelianNormConductorIdeal F (SourceQuadraticField F S₀ hζ e))
    (ArtinRay.abelianNormConductorIdeal_ne_bot F _) P.val = 0
  apply Finsupp.notMem_support_iff.mp
  rw [ArtinRay.abelianNormConductorIdeal_support, mem_ramifiedBaseFinitePlaces_iff]
  rintro ⟨W, hW, hram⟩
  let : W.asIdeal.LiesOver P.val.asIdeal := hW
  exact hram (sixthKummerIndividual_unramifiedAt (sourcePrimitiveRootSix F hζ) (u ^ 3) P.val
    (source_exterior_six_not_mem F S₀ P.val P.property) hu W.asIdeal hW.over.symm)

theorem sourceQuadraticConductor_exterior_one (e : E) (P : SourceExteriorPrime F S₀)
    (hP : e P = 1) :
    integralIdealFiniteModulus (sourceQuadraticConductor F S₀ hζ e)
      (sourceQuadraticConductor_ne_bot F S₀ hζ e) P.val = 1 := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  apply Nat.le_antisymm (sourceQuadraticConductor_exterior_le_one F S₀ hζ e P)
  apply Nat.one_le_iff_ne_zero.mpr
  intro he
  let u := sourcePrimeExponentUnit F hζ S₀ e
  let Q := GaloisIdealCharacter.primeAbove F (SourceQuadraticField F S₀ hζ e) P.val
  let W : HeightOneSpectrum (𝓞 (SourceQuadraticField F S₀ hζ e)) :=
    ⟨Q.val, Q.property.1, GaloisIdealCharacter.primeAbove_ne_bot F _ P.val⟩
  let : W.asIdeal.LiesOver P.val.asIdeal := ⟨Q.property.2.over⟩
  have hv : P.val.valuation F (u : F) = WithZero.exp (-1 : ℤ) := by
    rw [sourcePrimeExponentUnit_val, sourcePrimeExponentGenerator_valuation, hP]
    rfl
  have hur := ArtinRay.abelianNormConductorIdeal_unramified F (SourceQuadraticField F S₀ hζ e)
    P.val (Finsupp.notMem_support_iff.mpr he)
  exact quadraticKummer_ramified_of_valuation_one u P.val W hv hur

theorem sourceQuadraticConductor_exterior (e : E) (he : ∀ P, e P ≤ 1)
    (P : SourceExteriorPrime F S₀) :
    integralIdealFiniteModulus (sourceQuadraticConductor F S₀ hζ e)
      (sourceQuadraticConductor_ne_bot F S₀ hζ e) P.val = e P := by
  rcases Nat.eq_zero_or_pos (e P) with hp | hp
  · rw [sourceQuadraticConductor_exterior_zero F S₀ hζ e P hp, hp]
  · have hp1 : e P = 1 := Nat.le_antisymm (he P) hp
    rw [sourceQuadraticConductor_exterior_one F S₀ hζ e P hp1, hp1]

theorem sourceQuadraticConductor_wild_le (e : E) (P : HeightOneSpectrum (𝓞 F)) :
    integralIdealFiniteModulus (sourceQuadraticConductor F S₀ hζ e)
      (sourceQuadraticConductor_ne_bot F S₀ hζ e) P ≤ sixthLocalHenselDepth P := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  change integralIdealFiniteModulus
    (ArtinRay.abelianNormConductorIdeal F (SourceQuadraticField F S₀ hζ e))
    (ArtinRay.abelianNormConductorIdeal_ne_bot F _) _ ≤ _
  rw [ArtinRay.abelianNormConductorIdeal_modulus,
    ideleClassNorm_narrowFiniteConductor_eq_normDefiningModulus, ideleClassNormDefiningModulus_apply]
  exact ideleClassNormLocalHigherUnitExponent_min P
    (sixthKummerIndividual_higherUnit_le_chosenLocalNorm (sourcePrimitiveRootSix F hζ)
      ((sourcePrimeExponentUnit F hζ S₀ e : F) ^ 3)
      (pow_ne_zero _ (sourcePrimeExponentUnit F hζ S₀ e).ne_zero) P)

variable [IsTotallyComplex F]

def sourceQuadraticRayCharacter (e : E) :
    EvenIdealRayCharacter F (sourceQuadraticConductor F S₀ hζ e) :=
  ArtinRay.abelianNormConductorRayCharacter F _ (sourceQuadraticGaloisCharacter F S₀ hζ e)

theorem sourceQuadraticRayCharacter_idealHom (e : E) :
    (sourceQuadraticRayCharacter F S₀ hζ e).idealHom =
      GaloisIdealCharacter.idealHom F (SourceQuadraticField F S₀ hζ e)
        (sourceQuadraticGaloisCharacter F S₀ hζ e) := rfl

end
end ArtinMatthews.SourceEulerAssembly
