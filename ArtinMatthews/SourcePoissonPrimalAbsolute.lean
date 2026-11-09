module

public import ArtinMatthews.SourcePoissonPrimalExpansion
public import ArtinMatthews.SourceSLocalCompletionPoisson


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization
open SourcePhysical VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀

theorem sourcePoissonOriginalTest_summable_norm (t : SNormOne F S) (V : ℝ) :
    Summable (fun m : R => ‖sourcePoissonOriginalTest F S₀ hζ t V m‖) := by
  let : IsTotallyComplex F := source_isTotallyComplex F hζ
  exact sourceSLocalDilationProbe_summable_norm F (sourceHilbertSeed F S₀)
    ((t : SWholeUnits F S) * sLocalPositiveScaling F hζ S V)

variable [IsTotallyComplex F] {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

/-- The original density expands into the genuine periodic blocks with all
the summability of the actual dilated test discharged. -/
theorem sourcePoissonOriginalDensity_eq_primalExpanded_actual
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X Y Z : ℝ) (hZ : 0 < Z) (t : SNormOne F S) :
    sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t =
      sourcePoissonPrimalExpandedDensity F S₀ hζ η hBad X Y Z t :=
  sourcePoissonOriginalDensity_eq_primalExpanded F S₀ hζ η hBad X Y Z hZ t
    (fun s => sourcePoissonOriginalTest_summable_norm F S₀ hζ t
      ((sourcePrimeExponentNorm F S₀ s : ℝ) * X))

end
end ArtinMatthews.SourceEulerAssembly
