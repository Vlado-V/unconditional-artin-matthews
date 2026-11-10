module

public import ArtinMatthews.SourcePoissonInitialRows
public import ArtinMatthews.SourcePoissonTripleKernel
public import ArtinMatthews.SourceSLocalProbeMellin
public import ArtinMatthews.SourceSLocalProbeHolomorphic
public import ArtinMatthews.SourceSLocalProbeVertical
public import ArtinMatthews.VaryingKummerAnalyticSmoothMellin
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
open VaryingKummerAnalytic QuadraticWeil SourcePhysical
open scoped NumberField Classical ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

omit [IsTotallyComplex F] in
theorem sourceSLocalProbeMellin_continuous_vertical (v : InfinitePlace F) {a : ℝ} (ha : 0 < a) :
    Continuous (fun t : ℝ => sourceSLocalProbeMellin F hζ (sourceHilbertSet F S₀) v (sourcePoissonVertical a t)) :=
  (sourceSLocalProbeMellin_analyticOnNhd F hζ (sourceHilbertSet F S₀) v).continuousOn.comp_continuous
    (sourcePoissonVertical_continuous a) (fun t => by simpa [sourcePoissonVertical_re] using ha)

/-- Absolute integrability on the paper's initial three contours for the actual probe,
the original coefficient series and a smooth compact weight on the positive line. -/
theorem sourcePoissonInitialContour_integrable (v : InfinitePlace F)
    {X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (W₁ : ℝ → ℂ) (hcompact : HasCompactSupport W₁)
    (hpositive : tsupport W₁ ⊆ Set.Ioi 0) (hsmooth : ContDiff ℝ ∞ W₁)
    (U : Finset {u : sourceRing F S₀ // u ≠ 0}) :
    Integrable (sourcePoissonTripleKernel X Y Z 4 4 2
      (fun t => mellin W₁ (sourcePoissonVertical 4 t))
      (fun t => sourceSLocalProbeMellin F hζ (sourceHilbertSet F S₀) v (sourcePoissonVertical 2 t))
      (sourcePoissonInitialRows F S₀ hζ hS η U)) sourcePoissonHeightMeasure := by
  apply sourcePoissonTripleKernel_integrable hX hY hZ
    (B := sourcePoissonInitialRowBound F S₀ U)
  · exact smoothMellin_verticalIntegrable W₁ hcompact hpositive hsmooth 4
  · exact sourceSLocalProbeMellin_verticalIntegrable F hζ (sourceHilbertSet F S₀) v 2 (by norm_num)
  · exact ((smoothMellin_entire W₁ hcompact hpositive hsmooth.continuous).continuous.comp
      (sourcePoissonVertical_continuous 4)).measurable
  · exact (sourceSLocalProbeMellin_continuous_vertical F S₀ hζ v (by norm_num)).measurable
  · exact sourcePoissonInitialRows_measurable F S₀ hζ hS η U
  · exact sourcePoissonInitialRows_norm_le F S₀ hζ hS η U

end
end ArtinMatthews.SourceEulerAssembly
