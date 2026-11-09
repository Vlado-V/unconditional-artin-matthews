module

public import ArtinMatthews.SourcePoissonActualFrequencyNorm
public import ArtinMatthews.SourcePoissonInfiniteRows
public import ArtinMatthews.SourcePoissonOrbitAbsolute
public import ArtinMatthews.SourceProbeW1Mellin


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)

local notation "U" => sourceFrequencyRepresentative F hζ S₀

def sourcePoissonActualOrbitSeries (X Y Z : ℝ) : ℂ :=
  ∑' u : SourceFrequencyRepresentativeIndex F S₀, ∑' a : SourceExponentCoordinates F S₀,
    sourcePoissonOrbitTerm F S₀ hζ hS η v sourceProbeW1Complex X Y Z (U u) a

def sourcePoissonActualInitialKernel (X Y Z : ℝ) : SourcePoissonHeights → ℂ :=
  sourcePoissonTripleKernel X Y Z 4 4 2
    (fun y => sourceProbeW1Mellin (sourcePoissonVertical 4 y))
    (fun y => sourceSLocalProbeMellin F hζ (sourceHilbertSet F S₀) v (sourcePoissonVertical 2 y))
    (fun p => ∑' u : SourceFrequencyRepresentativeIndex F S₀,
      sourcePoissonOneRow F S₀ hζ hS η (U u) p)

/-- The original infinite frequency orbit sum with the constructed local probe
and compact weight equals the exact three-line Mellin expression. -/
theorem sourcePoissonActualOrbitSeries_eq_initialContour {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    let G := sourcePoissonActualInitialKernel F S₀ hζ hS η v X Y Z
    Integrable G sourcePoissonHeightMeasure ∧
      Summable (fun u : SourceFrequencyRepresentativeIndex F S₀ =>
        ‖∑' a : SourceExponentCoordinates F S₀,
          sourcePoissonOrbitTerm F S₀ hζ hS η v sourceProbeW1Complex X Y Z (U u) a‖) ∧
      sourcePoissonActualOrbitSeries F S₀ hζ hS η v X Y Z =
        sourcePoissonNormalization ^ 3 * ∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, G ((tw, tz), tξ) := by
  let : Countable (SourceFrequencyRepresentativeIndex F S₀) :=
    sourcePoissonActualFrequency_countable F S₀
  exact sourcePoissonOrbitSeries_countable_initialContours F S₀ hζ hS η v sourceProbeW1Complex
    sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support sourceProbeW1Complex_contDiff
    hX hY hZ U (sourcePoissonActualFrequencyNorm_summable F S₀ hζ)

theorem sourcePoissonActualOrbitRow_summable_norm {X Y Z : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (u : SourceFrequencyRepresentativeIndex F S₀) :
    Summable (fun a : SourceExponentCoordinates F S₀ =>
      ‖sourcePoissonOrbitTerm F S₀ hζ hS η v sourceProbeW1Complex X Y Z (U u) a‖) :=
  sourcePoissonOrbitRow_summable_norm F S₀ hζ hS η v sourceProbeW1Complex
    sourceProbeW1Complex_compact sourceProbeW1Complex_positive_support sourceProbeW1Complex_contDiff
    hX hY hZ (U u)

end
end ArtinMatthews.SourceEulerAssembly
