module

public import ArtinMatthews.SourcePoissonOriginalContourJoin
public import ArtinMatthews.SourcePoissonNestedDualReindex


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical MeasureTheory
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)
local notation "S" => sourceHilbertSet F S₀
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v
local notation "μ" => sNormOneQuotientMeasure F S ν

/-- The original physical probe equals the actual orbit sum with the exact
self-dual additive and induced norm-one quotient Haar measures. -/
theorem sourcePoissonOriginalIntegral_eq_actualOrbitSeries
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    Integrable (sourcePoissonOriginalQuotientDensity F S₀ hζ η hBad X Y Z) μ ∧
      sourcePoissonOriginalIntegral F S₀ hζ η v hBad X Y Z =
        sourcePoissonActualOrbitSeries F S₀ hζ hBad η v X Y Z :=
  sourcePoissonOriginalIntegral_of_nestedDual_ae F S₀ hζ η v hBad hX hY hZ
    (sourcePoissonNestedDualDensity_ae_eq_literal F S₀ hζ hBad η v hX hY hZ)

/-- Exact source identities (Poisson-probe) to (poisson-mellin) on the
paper's initial three contours, with absolute integrability on both sides. -/
theorem sourcePoissonOriginalIntegral_eq_initialContours
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    let G := sourcePoissonActualInitialKernel F S₀ hζ hBad η v X Y Z
    Integrable (sourcePoissonOriginalQuotientDensity F S₀ hζ η hBad X Y Z) μ ∧
      Integrable G sourcePoissonHeightMeasure ∧
      sourcePoissonOriginalIntegral F S₀ hζ η v hBad X Y Z =
        sourcePoissonNormalization ^ 3 * ∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, G ((tw, tz), tξ) := by
  have hI := sourcePoissonOriginalIntegral_eq_actualOrbitSeries F S₀ hζ η v hBad hX hY hZ
  have hM := sourcePoissonActualOrbitSeries_eq_initialContour F S₀ hζ hBad η v hX hY hZ
  exact ⟨hI.1, hM.1, hI.2.trans hM.2.2⟩

end
end ArtinMatthews.SourceEulerAssembly
