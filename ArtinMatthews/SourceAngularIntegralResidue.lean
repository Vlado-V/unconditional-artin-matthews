module

public import ArtinMatthews.SourceAngularResidueValue


set_option backward.privateInPublic true
@[expose] public section

/-! Comparison of the canonical integral residue symbol and the oriented
complex angular character at an arbitrary prime-to-prime numerator. -/
namespace ArtinMatthews.AngularLambda
open NumberField IsDedekindDomain AlgebraicNumberTheory.PowerResidueSymbols
open VaryingKummerAnalytic OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F] {ζ : F}

theorem sourceComplexEmbedding_integralResidue (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 F)) (hsix : (6 : 𝓞 F) ∉ P.asIdeal)
    (hmu : (primitiveRoots 6 F).Nonempty) (a : 𝓞 F) (ha : a ∉ P.asIdeal) :
    sourceComplexEmbedding hζ
        (((primeIdealPowerResidueSymbol F P 6 hmu (probePrimeNorm_coprime_six F P hsix)
          a ha : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) =
      cyclotomicAngularResidueCharacter hζ P hsix (Ideal.Quotient.mk P.asIdeal a) := by
  let : Algebra BaseField F := baseAlgebraOfTwelve hζ
  let u := primeIdealResidueUnit F P a ha
  have hr : probeIntegralSixthRoot F (probeAngularIntegralCharacter F P hsix u)
      (probeAngularIntegralCharacter_pow_six F P hsix u) =
      (primeIdealPowerResidueSymbol F P 6 hmu (probePrimeNorm_coprime_six F P hsix)
        a ha : rootsOfUnity 6 (𝓞 F)) := probeAngularIntegralCharacter_eq_symbol F P hsix hmu a ha
  have hv := congrArg (fun z : rootsOfUnity 6 (𝓞 F) =>
    sourceComplexEmbedding hζ (((z : (𝓞 F)ˣ) : 𝓞 F) : F)) hr
  change sourceComplexEmbedding hζ
      ((algebraMap BaseIntegers (𝓞 F) (probeAngularIntegralCharacter F P hsix u) : 𝓞 F) : F) = _ at hv
  apply hv.symm.trans
  apply (sourceComplexEmbedding_baseInteger hζ _).trans
  symm
  change globalAngularResidueCharacter F P hsix (Ideal.Quotient.mk P.asIdeal a) = _
  simpa only [u, primeIdealResidueUnit, Units.val_mk0] using
    (probeAngularIntegralCharacter_complex F P hsix (u : 𝓞 F ⧸ P.asIdeal))

end
end ArtinMatthews.AngularLambda
