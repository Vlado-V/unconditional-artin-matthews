module

public import ArtinMatthews.SourceThetaLogSheet
public import ArtinMatthews.SourceSLocalSheetMellin
public import ArtinMatthews.SourceSLocalWholeMellin
public import ArtinMatthews.SourceSLocalProbeSheetIdentity
public import ArtinMatthews.SourceSLocalRadialInvariance
public import ArtinMatthews.SourceSLocalRadialSheet
public import ArtinMatthews.SourceSLocalSheetBorel
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Literal Haar sheets of the rotated tensors in source03. The
dependent complex log radius is the total log norm minus the
retained log norm. This holds for both the signed and absolute integrals. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ArtinMatthews.SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)

local notation "hv" => sourceSLocalComplexPlace K hζ v
local notation "ν" => sourceSLocalNormalizedSheetMeasure K hζ S v
local notation "μOther" => sourceSLocalOtherUnitMeasure K hζ S v
local notation "N" => sourceSheetOtherNorm S v
local notation "Other" => SNormOneOtherUnits S v

def sourceThetaSLocalTensor (g : Circle → ℝ → ℂ) (G : Other → ℂ) (x : SWholeUnits K S) : ℂ :=
  let z := sourceComplexPlaceUnitsEquiv hv (x.1 v)
  g (sourceComplexUnitAngle z) (sourceComplexUnitLogNorm z) * G (sourceSheetOther S v x)

def sourceThetaSLocalSheet (g : Circle → ℝ → ℂ) (G : Other → ℂ) : ℝ → ℂ :=
  sourceSLocalSheetProfile S ν hζ (sourceThetaSLocalTensor K S hζ v g G)

def sourceThetaSLocalSheetAbs (g : Circle → ℝ → ℂ) (G : Other → ℂ) (T : ℝ) : ℝ :=
  ∫ x : SNormOne K S, ‖sourceThetaSLocalTensor K S hζ v g G
    ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)‖ ∂ν

private theorem sourceThetaSLocalTensor_radial (g : Circle → ℝ → ℂ) (G : Other → ℂ)
    (t : ℝ) (a : Circle × Other) :
    sourceThetaSLocalTensor K S hζ v g G (sourceSLocalRadialSheet S hv a t) =
      sourceThetaLogSheetIntegrand N G g t a := by
  let z := sourceComplexPlaceUnitsEquiv hv ((sourceSLocalRadialSheet S hv a t).1 v)
  have hz : z = sourceComplexRadialUnit (t - Real.log (N a.2)) * Circle.toUnits a.1 := by
    apply Units.ext
    change (sourceComplexPlaceUnitsEquiv hv ((sourceSLocalRadialSheet S hv a t).1 v) : ℂ) = _
    rw [sourceSLocalRadialSheet_chosen, sourceSheetComplexCoordinate]
    rfl
  change g (sourceComplexUnitAngle z) (sourceComplexUnitLogNorm z) *
    G (sourceSheetOther S v (sourceSLocalRadialSheet S hv a t)) = _
  rw [hz, sourceComplexRadialUnit_mul_angle_angle, sourceComplexRadialUnit_mul_angle_logNorm,
    sourceSLocalRadialSheet_other, sourceThetaLogSheetIntegrand]

private theorem sourceThetaSLocalTensor_integral_exp (g : Circle → ℝ → ℂ) (G : Other → ℂ)
    (φ : ℂ → ℂ) (t : ℝ) :
    (∫ x : SNormOne K S, φ (sourceThetaSLocalTensor K S hζ v g G
        ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S (Real.exp t))) ∂ν) =
      ∫ a, φ (sourceThetaLogSheetIntegrand N G g t a) ∂sourceCircleHaar.prod μOther := by
  have : BorelSpace Other := sourceSheetOtherUnits_product_borel S v
  have : Measure.IsHaarMeasure ν := sourceSLocalNormalizedSheetMeasure_isHaar K hζ S v
  change (∫ x : SNormOne K S, (φ ∘ sourceThetaSLocalTensor K S hζ v g G)
    ((x : SWholeUnits K S) * sLocalPositiveScaling K hζ S (Real.exp t)) ∂ν) = _
  rw [← sourceSLocal_radial_integral_eq_literal S ν hζ hv
      (φ ∘ sourceThetaSLocalTensor K S hζ v g G) t,
    sourceSLocalNormalizedSheetMeasure, sourceSNormOneSheetMeasure_integral]
  apply integral_congr_ae
  filter_upwards with a
  change φ (sourceThetaSLocalTensor K S hζ v g G (sourceSLocalRadialSheet S hv a t)) = _
  rw [sourceThetaSLocalTensor_radial K S hζ v]

theorem sourceThetaSLocalSheet_exp (g : Circle → ℝ → ℂ) (G : Other → ℂ) (t : ℝ) :
    sourceThetaSLocalSheet K S hζ v g G (Real.exp t) = sourceThetaLogSheet μOther N G g t :=
  sourceThetaSLocalTensor_integral_exp K S hζ v g G id t

theorem sourceThetaSLocalSheetAbs_exp (g : Circle → ℝ → ℂ) (G : Other → ℂ) (t : ℝ) :
    sourceThetaSLocalSheetAbs K S hζ v g G (Real.exp t) = sourceThetaLogSheetAbs μOther N G g t := by
  have h := sourceThetaSLocalTensor_integral_exp K S hζ v g G (fun z => (‖z‖ : ℂ)) t
  apply Complex.ofReal_injective
  unfold sourceThetaSLocalSheetAbs sourceThetaLogSheetAbs
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  exact h

end
end ArtinMatthews.SourceReflection
