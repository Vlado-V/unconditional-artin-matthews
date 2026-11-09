module

public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SourceAngularGaussCube
public import ArtinMatthews.SourceGaussPrimeValue


set_option backward.privateInPublic true
@[expose] public section

/-! The literal global source Theta at a prime is the actual local
Gauss Vartheta in the standard generator phase, including chi(4)^(-1). -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField IsDedekindDomain AllowedGenerators AngularLambda QuadraticWeil
open SIntegerPrincipalization SIntegerQuotient SIntegerFourier StandardAdelic
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local instance sourceThetaQuotientField (P : HeightOneSpectrum (𝓞 F)) :
    Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field _
local instance sourceThetaQuotientFinite (P : HeightOneSpectrum (𝓞 F)) :
    Finite (𝓞 F ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
local instance sourceThetaQuotientFintype (P : HeightOneSpectrum (𝓞 F)) :
    Fintype (𝓞 F ⧸ P.asIdeal) := Fintype.ofFinite _

def sourcePrimeResiduePhase (P : SourceExteriorPrime F S₀) : AddChar ((𝓞 F) ⧸ P.val.asIdeal) ℂ :=
  residueSourcePhase (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)

theorem sourcePrimeExponentIdeal_single (P : SourceExteriorPrime F S₀) (n : ℕ) :
    sourcePrimeExponentIdeal F S₀ (Finsupp.single P n) = P.val.asIdeal ^ n :=
  Finsupp.prod_single_index
    (h := fun Q : SourceExteriorPrime F S₀ => fun k : ℕ => Q.val.asIdeal ^ k)
    (a := P) (b := n) (pow_zero _)

variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
include hS

theorem sourceExteriorPrime_not_traceBad (P : SourceExteriorPrime F S₀) :
    P.val ∉ traceBadPlaces F := by
  intro h
  apply P.property
  apply hS
  exact Finset.mem_union_left _ h

theorem sourcePrimeResiduePhase_primitive (P : SourceExteriorPrime F S₀) :
    (sourcePrimeResiduePhase F hζ S₀ P).IsPrimitive :=
  residueSourcePhase_primitive (sourceHilbertSeed F S₀) P.val P.property _
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) (sourceExteriorPrime_not_traceBad F S₀ hS P)

theorem sourcePrimeLocalLambda (P : SourceExteriorPrime F S₀) :
    probeGaussLocalLambda (reflectionPrimeCharacters F hζ S₀ P) (sourcePrimeResiduePhase F hζ S₀ P) =
      cyclotomicAngularIdeal hζ P.val.asIdeal := by
  have h := sourceAngularGammaTwo_cube F hζ (sourceHilbertSeed F S₀) P.val P.property
    (sourceAllowedPrimeGenerator F hζ S₀ P) (sourceAllowedPrimeGenerator_ideal F hζ S₀ P)
    (sourceExteriorPrime_not_traceBad F S₀ hS P) (source_exterior_six_not_mem F S₀ P.val P.property)
  exact (congrArg (fun z : ℂ => -z) h).trans (neg_neg _)

variable [IsTotallyComplex F]

theorem sourcePrimeLocalG (P : SourceExteriorPrime F S₀) :
    ((sourceGaussHeckeCharacter F hζ S₀ hS).idealHom
      (integralIdealFractionalUnit P.val.asIdeal P.val.ne_bot) : ℂ) =
        probeGaussLocalG (reflectionPrimeCharacters F hζ S₀ P) (sourcePrimeResiduePhase F hζ S₀ P) :=
  sourceGaussHeckeCharacter_prime F hζ S₀ hS P.val P.property _
    (sourceAllowedPrimeGenerator_ideal F hζ S₀ P) (sourceAllowedPrimeUnit_allowed F hζ S₀ P)

theorem reflectionThetaValue_prime {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
    (P : SourceExteriorPrime F S₀) :
    reflectionThetaValue F hζ S₀ hS η (Finsupp.single P 1) =
      probeGaussLocalVartheta (reflectionPrimeCharacters F hζ S₀ P)
        (sourcePrimeResiduePhase F hζ S₀ P) (η.allCoefficient P.val.asIdeal) := by
  have hI : sourcePrimeExponentIdeal F S₀ (Finsupp.single P 1) = P.val.asIdeal := by
    rw [sourcePrimeExponentIdeal_single, pow_one]
  have hU : integralIdealFractionalUnit (sourcePrimeExponentIdeal F S₀ (Finsupp.single P 1))
      (sourcePrimeExponentIdeal_ne_bot F S₀ _) = integralIdealFractionalUnit P.val.asIdeal P.val.ne_bot := by
    apply Units.ext
    exact congrArg (fun I : Ideal (𝓞 F) => (I : FractionalIdeal (𝓞 F)⁰ F)) hI
  dsimp only [reflectionThetaValue, probeGaussLocalVartheta]
  rw [hU, sourcePrimeLocalG F hζ S₀ hS P, hI, sourcePrimeLocalLambda F hζ S₀ hS P]

end
end ArtinMatthews.VaryingKummerAnalytic
