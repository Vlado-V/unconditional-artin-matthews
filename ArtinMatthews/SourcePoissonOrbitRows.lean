module

public import ArtinMatthews.SourcePoissonOrbitInversion
public import ArtinMatthews.SourcePoissonContourInterchange


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain MeasureTheory AllowedGenerators
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical ContDiff BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
variable (v : InfinitePlace F)

local notation "q" => sourcePrimeExponentNorm F S₀
local notation "qu" => sourcePoissonFrequencyNorm F S₀
local notation "Ŵ" => fun W y => mellin W (sourcePoissonVertical 4 y)
local notation "M̂" => fun y => sourceSLocalProbeMellin F hζ (sourceHilbertSet F S₀) v (sourcePoissonVertical 2 y)

def sourcePoissonOrbitCoefficient (u : sourceRing F S₀)
    (a : SourceExponentCoordinates F S₀) : ℂ :=
  reflectionGammaTwo F hζ S₀ a.1.val *
    reflectionThetaValue F hζ S₀ hS η (a.1.val + 3 • a.2.1) *
    sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀)
      a.2.2.1 (a.1.val + 3 • a.2.1)
      (u * sourcePrimeExponentGenerator F hζ S₀ a.2.2.2 ^ 6)

/-- The exact summand of the physical orbit series, with the original
normalized quadratic Gauss coefficient and finite Fourier row. -/
def sourcePoissonOrbitTerm (W₁ : ℝ → ℂ) (X Y Z : ℝ)
    (u : {u : sourceRing F S₀ // u ≠ 0}) (a : SourceExponentCoordinates F S₀) : ℂ :=
  sourcePoissonOrbitWeight F (sourceHilbertSet F S₀) hζ v W₁ X Y Z (q a.1.val) (q a.2.1)
    (q a.2.2.1) (q a.2.2.2) (qu u) * sourcePoissonOrbitCoefficient F S₀ hζ hS η u.val a

theorem sourcePoissonOrbitTerm_eq_initialContour
    (W₁ : ℝ → ℂ) (hcompact : HasCompactSupport W₁)
    (hpositive : tsupport W₁ ⊆ Set.Ioi 0) (hsmooth : ContDiff ℝ ∞ W₁)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : {u : sourceRing F S₀ // u ≠ 0}) (a : SourceExponentCoordinates F S₀) :
    sourcePoissonOrbitTerm F S₀ hζ hS η v W₁ X Y Z u a =
      sourcePoissonNormalization ^ 3 * ∫ p : SourcePoissonHeights,
        sourcePoissonFrequencyKernel F S₀ X Y Z (Ŵ W₁) M̂ u p *
        sourceGlobalEulerTerm F hζ S₀ hS η u.val (sourcePoissonVertical 4 p.2)
          (sourcePoissonVertical 4 p.1.1) (sourcePoissonVertical 2 p.1.2) a
        ∂sourcePoissonHeightMeasure := by
  have hq (b : SourcePrimeExponents F S₀) : (0 : ℝ) < q b :=
    Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ b)
  unfold sourcePoissonOrbitTerm
  rw [sourcePoissonOrbitWeight_eq_initialContour F (sourceHilbertSet F S₀) hζ v W₁ hcompact hpositive hsmooth
    hX hY hZ (hq _) (hq _) (hq _) (hq _) (sourcePoissonFrequencyNorm_pos F S₀ u),
    mul_assoc, ← integral_mul_const]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  simp only [sourcePoissonFrequencyKernel, sourcePoissonTripleKernel, sourceGlobalEulerTerm,
    sourcePoissonOrbitCoefficient, Complex.ofReal_natCast, neg_mul,
    show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring]
  ac_rfl

/-- The entire four-ideal physical series for a fixed nonzero frequency
equals its absolutely integrable initial contour. -/
theorem sourcePoissonOrbitRow_eq_initialContour
    (W₁ : ℝ → ℂ) (hcompact : HasCompactSupport W₁)
    (hpositive : tsupport W₁ ⊆ Set.Ioi 0) (hsmooth : ContDiff ℝ ∞ W₁)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (u : {u : sourceRing F S₀ // u ≠ 0}) :
    (∑' a : SourceExponentCoordinates F S₀, sourcePoissonOrbitTerm F S₀ hζ hS η v W₁ X Y Z u a) =
      sourcePoissonNormalization ^ 3 * ∫ p : SourcePoissonHeights,
        sourcePoissonFrequencyKernel F S₀ X Y Z (Ŵ W₁) M̂ u p *
        sourceGlobalCalF F hζ S₀ hS η u.val (sourcePoissonVertical 4 p.2)
          (sourcePoissonVertical 4 p.1.1) (sourcePoissonVertical 2 p.1.2)
        ∂sourcePoissonHeightMeasure := by
  have hW := smoothMellin_verticalIntegrable W₁ hcompact hpositive hsmooth 4
  have hM := sourceSLocalProbeMellin_verticalIntegrable F hζ (sourceHilbertSet F S₀) v 2 (by norm_num)
  have hWm : Measurable (Ŵ W₁) :=
    ((smoothMellin_entire W₁ hcompact hpositive hsmooth.continuous).continuous.comp
      (sourcePoissonVertical_continuous 4)).measurable
  have hMm : Measurable M̂ :=
    (sourceSLocalProbeMellin_continuous_vertical F S₀ hζ v (by norm_num)).measurable
  simp_rw [sourcePoissonOrbitTerm_eq_initialContour F S₀ hζ hS η v W₁ hcompact hpositive
    hsmooth hX hY hZ u]
  rw [tsum_mul_left]
  exact congrArg (fun b : ℂ => sourcePoissonNormalization ^ 3 * b)
    (sourcePoissonInitialRow_integral_eq_tsum F S₀ hζ hS η hX hY hZ
      (Ŵ W₁) M̂ hW hM hWm hMm u).symm

end
end ArtinMatthews.SourceEulerAssembly
