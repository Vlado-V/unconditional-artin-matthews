module

public import ArtinMatthews.SourcePoissonActualInitialContour
public import ArtinMatthews.SourcePoissonOriginalQuotient
public import ArtinMatthews.SourcePoissonNestedDualReindex
public import ArtinMatthews.SourcePoissonOriginalContourJoin
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
