module

public import ArtinMatthews.SourcePoissonOriginalMeasurable
public import ArtinMatthews.SourcePoissonActualPrimalDual
public import ArtinMatthews.SourcePoissonActualInitialContour


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
local notation "Q" => SNormOneSixthQuotient F S
local notation "π" => sNormOneSixthQuotientMap F S
local notation "D" => sNormOneFundamentalSet F S
local notation "ν" => sourceSLocalNormalizedSheetMeasure F hζ S v
local notation "μ" => sNormOneQuotientMeasure F S ν

theorem sourcePoissonOriginalIntegral_of_nestedDual_ae
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hDual : ∀ᵐ t : SNormOne F S ∂(ν).restrict D,
      sourcePoissonNestedDualDensity F S₀ hζ hBad η X Y Z t =
        sourcePoissonLiteralFourierSeries F S₀ hζ hBad η X Y Z t) :
    Integrable (sourcePoissonOriginalQuotientDensity F S₀ hζ η hBad X Y Z) μ ∧
      sourcePoissonOriginalIntegral F S₀ hζ η v hBad X Y Z =
        sourcePoissonActualOrbitSeries F S₀ hζ hBad η v X Y Z := by
  let f := sourcePoissonOriginalQuotientDensity F S₀ hζ η hBad X Y Z
  let L := sourcePoissonLiteralFourierSeries F S₀ hζ hBad η X Y Z
  have hf : Measurable f := sourcePoissonOriginalQuotientDensity_measurable F S₀ hζ η hBad X Y Z
  have hπ : Measurable (π : SNormOne F S → Q) := QuotientGroup.measurable_coe
  have hL := sourcePoissonLiteralFundamentalIntegral F S₀ hζ hBad η v hX hY hZ
  have he : (f ∘ π) =ᵐ[(ν).restrict D] L := by
    filter_upwards [hDual] with t ht
    exact (sourcePoissonOriginalQuotientDensity_mk F S₀ hζ η hBad X Y Z t).trans
      ((sourcePoissonOriginalDensity_eq_nestedDual F S₀ hζ η hBad hX Y hZ t).trans ht)
  have hInt : Integrable f μ :=
    (integrable_map_measure hf.aestronglyMeasurable hπ.aemeasurable).mpr (hL.1.congr he.symm)
  refine ⟨hInt, ?_⟩
  change (∫ t, f t ∂μ) = _
  calc
    _ = ∫ t in D, f (π t) ∂ν := sNormOneQuotient_integral F S ν f hInt
    _ = ∫ t in D, L t ∂ν := integral_congr_ae he
    _ = _ := hL.2

theorem sourcePoissonOriginalInitialContour_of_nestedDual_ae
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hDual : ∀ᵐ t : SNormOne F S ∂(ν).restrict D,
      sourcePoissonNestedDualDensity F S₀ hζ hBad η X Y Z t =
        sourcePoissonLiteralFourierSeries F S₀ hζ hBad η X Y Z t) :
    let G := sourcePoissonActualInitialKernel F S₀ hζ hBad η v X Y Z
    Integrable G sourcePoissonHeightMeasure ∧
      sourcePoissonOriginalIntegral F S₀ hζ η v hBad X Y Z =
        sourcePoissonNormalization ^ 3 * ∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, G ((tw, tz), tξ) := by
  have hI := sourcePoissonOriginalIntegral_of_nestedDual_ae F S₀ hζ η v hBad hX hY hZ hDual
  have hC := sourcePoissonActualOrbitSeries_eq_initialContour F S₀ hζ hBad η v hX hY hZ
  exact ⟨hC.1, hI.2.trans hC.2.2⟩

end
end ArtinMatthews.SourceEulerAssembly
