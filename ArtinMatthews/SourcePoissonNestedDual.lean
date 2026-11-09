module

public import ArtinMatthews.SourcePoissonPhysicalScalars
public import ArtinMatthews.SourcePoissonLiteralQuotientUnfold


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "C" => ReflectionSquarefreeExponents F S₀
local notation "H" => SourceNonzeroFrequency F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀

abbrev SourcePoissonNestedDualIndex := E × ((C × E) × H)

variable [IsTotallyComplex F]

/-- The literal dual Fourier value at a frequency in the actual source ring. -/
def sourcePoissonNestedDualTransform (X : ℝ) (t : SNormOne F S) (s A : E) (h : R) : ℂ :=
  sourceSLocalCompletionFourier F S (sourceSLocalCompletionProbe F S)
    (sourceSLocalUnitAdditivePoint F S
      ((t : SWholeUnits F S) * sLocalPositiveScaling F hζ S ((q s : ℝ) * X)) *
      sLocalRingDiagonal F S ((h : F) / ((a s * a A : R) : F)))

theorem sourcePoissonNestedDualTransform_zero (X : ℝ) (t : SNormOne F S) (s A : E) :
    sourcePoissonNestedDualTransform F S₀ hζ X t s A 0 = 0 := by
  unfold sourcePoissonNestedDualTransform
  rw [show ((0 : R) : F) = 0 from rfl, zero_div, map_zero, mul_zero,
    sourceSLocalCompletionProbe_fourier_zero]

variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

/-- The original signed coefficient, with the exact physical Poisson prefactor. -/
def sourcePoissonNestedDualScalar (X Y Z : ℝ) (s : E) (c : C) (n : E) (h : R) : ℂ :=
  let A := c.val + 3 • n
  (Y : ℂ)⁻¹ * sourceProbeW1Complex ((q s : ℝ) / Y) *
    ((Real.sqrt X / (q A : ℝ) : ℝ) : ℂ) *
    sourcePoissonPhysicalGaussianCoefficient F S₀ hζ η hBad c n Z *
      sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀) s A h

def sourcePoissonNestedDualTerm (X Y Z : ℝ) (t : SNormOne F S)
    (s : E) (c : C) (n : E) (h : R) : ℂ :=
  sourcePoissonNestedDualScalar F S₀ hζ hBad η X Y Z s c n h *
    sourcePoissonNestedDualTransform F S₀ hζ X t s (c.val + 3 • n) h

theorem sourcePoissonNestedDualTerm_zero (X Y Z : ℝ) (t : SNormOne F S)
    (s : E) (c : C) (n : E) :
    sourcePoissonNestedDualTerm F S₀ hζ hBad η X Y Z t s c n 0 = 0 := by
  rw [sourcePoissonNestedDualTerm, sourcePoissonNestedDualTransform_zero, mul_zero]

/-- The nested dual density before changing the nonzero frequency index to orbits. -/
def sourcePoissonNestedDualDensity (X Y Z : ℝ) (t : SNormOne F S) : ℂ :=
  ∑' s : E, ∑' p : C × E, ∑' h : H,
    sourcePoissonNestedDualTerm F S₀ hζ hBad η X Y Z t s p.1 p.2 h.val

end
end ArtinMatthews.SourceEulerAssembly
