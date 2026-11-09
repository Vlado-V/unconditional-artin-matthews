module

public import ArtinMatthews.SourceSLocalAdditiveProbeAnalysis
public import ArtinMatthews.SourceSLocalProbeSheetIdentity
public import ArtinMatthews.SourceProbeW1Mellin
public import ArtinMatthews.SourceFiniteFourierNormalization
public import ArtinMatthews.ReflectionCoefficientConvergence
public import ArtinMatthews.SLocalNormOneUnfold


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators
open VaryingKummerAnalytic QuadraticWeil SourcePhysical SIntegerFourier SIntegerQuotient
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀
local notation "q" => sourcePrimeExponentNorm F S₀

/-- The residue value on the literal quotient by the chosen allowed generator. -/
def sourcePoissonQuotientResidue (e : SourcePrimeExponents F S₀)
    (x : R ⧸ Ideal.span {a e}) : ℂ :=
  reflectionExponentResidueValue F hζ S₀ e (Quotient.out x)

/-- The actual finite character Gauss sum from the physical probe. -/
def sourcePoissonOriginalGauss (e : SourcePrimeExponents F S₀) (m : R) : ℂ :=
  sourceResidueGauss (sourceHilbertSeed F S₀) (a e)
    (sourcePrimeExponentGenerator_ne_zero F hζ S₀ e)
    (sourcePoissonQuotientResidue F S₀ hζ e) m

variable [IsTotallyComplex F]
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)

/-- The literal point of W₀ on the original (m)-sum. -/
def sourcePoissonOriginalTest (t : SNormOne F S) (T : ℝ) (m : R) : ℂ :=
  sourceSLocalCompletionProbe F S
    (sLocalRingDiagonal F S (m : F) * sourceSLocalUnitAdditivePoint F S
      (((t : SWholeUnits F S) * sLocalPositiveScaling F hζ S T)⁻¹))

theorem sourcePoissonOriginalTest_zero (t : SNormOne F S) (T : ℝ) :
    sourcePoissonOriginalTest F S₀ hζ t T 0 = 0 := by
  unfold sourcePoissonOriginalTest
  rw [show ((0 : R) : F) = 0 from rfl, map_zero, zero_mul, sourceSLocalCompletionProbe_zero]

/-- The literal sum on the norm-one group before descending to its sixth-power quotient. -/
def sourcePoissonOriginalDensity (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X Y Z : ℝ) (t : SNormOne F S) : ℂ :=
  let B : R → ℂ := fun m => @reflectionCoefficientRow F _ _ ζ hζ S₀ _ hBad J η m Z
  (Y : ℂ)⁻¹ * ∑' s : SourcePrimeExponents F S₀,
    sourceProbeW1Complex ((q s : ℝ) / Y) *
      ((Real.sqrt ((q s : ℝ) * X) : ℂ)⁻¹ *
        ∑' m : R,
          (sourcePoissonOriginalGauss F S₀ hζ s (-m) /
            (Real.sqrt (q s : ℝ) : ℂ)) *
          sourcePoissonOriginalTest F S₀ hζ t ((q s : ℝ) * X) m *
          B m)

/-- The original physical probe integrated with the normalized quotient measure. -/
def sourcePoissonOriginalIntegral (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    (X Y Z : ℝ) : ℂ :=
  let density : SNormOneSixthQuotient F S → ℂ := fun t =>
    sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z (Quotient.out t)
  ∫ t, density t ∂sNormOneQuotientMeasure F S (sourceSLocalNormalizedSheetMeasure F hζ S v)

end
end ArtinMatthews.SourceEulerAssembly
