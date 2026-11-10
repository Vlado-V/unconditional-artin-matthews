module

public import ArtinMatthews.ReflectionCoefficientRow
public import ArtinMatthews.SIntegerFiniteSourceFourier
public import ArtinMatthews.SourceProbeW1
public import ArtinMatthews.SourceSLocalAdditiveProbeBinding
public import ArtinMatthews.SourceSLocalAdditiveProbeAnalysis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
