module

public import ArtinMatthews.SourceLocalPhaseComparison
public import ArtinMatthews.ProbeIdealPhasePowers
public import ArtinMatthews.PrincipalAngularCorrection


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Gauss-Hecke Theta coefficient at a prime, with the exact
cubic residue multiplier from a change of primitive additive phase. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
variable (P : SourceExteriorPrime F S₀)

local notation "κ" => ((𝓞 F) ⧸ P.val.asIdeal)
local notation "χ" => reflectionPrimeCharacters F hζ S₀ P
local notation "ψ" => sourcePrimeResiduePhase F hζ S₀ P
local notation "η₀" => η.allCoefficient P.val.asIdeal
local instance sourceThetaPhaseField : Field κ := Ideal.Quotient.field _
local instance sourceThetaPhaseFinite : Finite κ := Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
local instance sourceThetaPhaseFintype : Fintype κ := Fintype.ofFinite _

theorem sourcePrimeTheta_mulShift (a : κˣ)
    (ha : ψ = (probeIdealResiduePhase F P.val).mulShift a) :
    reflectionThetaValue F hζ S₀ hS η (Finsupp.single P 1) =
      (χ a) ^ 3 * probeIdealGaussLocalVartheta F P.val χ η₀ := by
  have hLambda : probeGaussLocalLambda χ ψ = probeIdealGaussLocalLambda F P.val χ := by
    have h₆ := sourcePrimeCharacter_unit_pow_six F hζ S₀ P a
    have h₂₃ : ((χ a)⁻¹ ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show (2 : ℕ) * 3 = 6 by decide, inv_pow, h₆, inv_one]
    rw [probeGaussLocalLambda, probeIdealGaussLocalLambda,
      sourcePrimeGaussGamma_mulShift F hζ S₀ P a ha 2, mul_pow, h₂₃, one_mul]
  have hG : probeGaussLocalG χ ψ = (χ a)⁻¹ ^ 3 * probeIdealGaussLocalG F P.val χ := by
    simp only [probeGaussLocalG, probeIdealGaussLocalG, map_ofNat,
      sourcePrimeGaussGamma_mulShift F hζ S₀ P a ha 3]
    ring
  have hstar : star ((χ a)⁻¹) = χ a := by
    rw [star_inv₀, MulChar.star_apply', MulChar.inv_apply_eq_inv', inv_inv]
  rw [reflectionThetaValue_prime, probeGaussLocalVartheta, hLambda, hG, star_mul, star_pow,
    hstar, probeIdealGaussLocalVartheta]
  ring

theorem sourcePrimeTheta_sixth :
    reflectionThetaValue F hζ S₀ hS η (Finsupp.single P 1) ^ 6 =
      principalAngularThirdPhase hζ η P.val := by
  rw [reflectionThetaValue_prime,
    probeSexticGauss_vartheta_sixth χ (sourcePrimeCharacter_order F hζ S₀ P)
      (sourcePrimeCharacter_minus_one F hζ S₀ P) ψ (sourcePrimeResiduePhase_primitive F hζ S₀ hS P)
      (sourcePrimeResidue_char_ne_two F S₀ P), sourcePrimeLocalLambda F hζ S₀ hS P]
  rfl

end
end ArtinMatthews.SourceEulerAssembly
