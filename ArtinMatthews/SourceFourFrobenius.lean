module

public import ArtinMatthews.SourceAngularResidueValue
public import ArtinMatthews.KummerRowField


set_option backward.privateInPublic true
@[expose] public section

/-! The literal Frobenius character used by the Kummer correction of
four has the source's actual angular residue value. The complex
embedding and the finite-field power are both derived. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain
open AngularLambda VaryingKummerAnalytic
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] {ζ : F}
variable (hζ : IsPrimitiveRoot ζ 12)

theorem sourceFourFrobenius_value (P : HeightOneSpectrum (𝓞 F))
    (hsix : (6 : 𝓞 F) ∉ P.asIdeal) :
    letI : Algebra F ℂ := sourceComplexAlgebra hζ
    (sixthKummerRowCharacter (ζ := ζ ^ 2)
      (by simpa using hζ.pow_of_dvd (p := 2) (by decide) (by decide))
      {4} 4 (Finset.mem_singleton_self _) (by norm_num)
      (GaloisIdealCharacter.primeFrobenius F (sixthKummerRowField {4}) P) : ℂ) =
      cyclotomicAngularResidueCharacter hζ P hsix (4 : 𝓞 F ⧸ P.asIdeal) := by
  let : Algebra F ℂ := sourceComplexAlgebra hζ
  let E := sixthKummerRowField ({4} : Finset F)
  let α : E := sixthKummerRowRoot ({4} : Finset F) 4 (Finset.mem_singleton_self _)
  have hα : α ^ 6 = 4 := by
    simpa only [map_ofNat] using sixthKummerRowRoot_pow ({4} : Finset F) 4 (Finset.mem_singleton_self _)
  have hmu : (primitiveRoots 6 F).Nonempty := by
    refine ⟨ζ ^ 2, (mem_primitiveRoots (by decide : 0 < 6)).mpr ?_⟩
    simpa using hζ.pow_of_dvd (p := 2) (by decide) (by decide)
  have hr := frobenius_sixthRoot_four F E P hsix hmu
    (probePrimeNorm_coprime_six F P hsix) α hα
  change ((GaloisIdealCharacter.primeFrobenius F E P α / α : E) : ℂ) = _
  calc
    _ = sourceComplexEmbedding hζ
        (((AlgebraicNumberTheory.PowerResidueSymbols.primeIdealPowerResidueSymbol F P 6 hmu
          (probePrimeNorm_coprime_six F P hsix) 4
          (four_not_mem_of_six_not_mem F P hsix) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) :=
      congrArg (fun x : E => (x : ℂ)) hr
    _ = _ := sourceComplexEmbedding_fourResidue hζ P hsix hmu

end

end ArtinMatthews
