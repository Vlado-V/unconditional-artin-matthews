module

public import ArtinMatthews.SourceKPCuspAnisotropicTorus
public import ArtinMatthews.SourceKPCuspSobolev
public import ArtinMatthews.SourceKPCuspCartesianDerivative
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

/-! Anisotropic horizontal coercivity on the actual principal cusp with trace Haar measure. -/
namespace ArtinMatthews
open NumberField Module Module.Free MeasureTheory Topology UnitAddTorus
open scoped NumberField Classical BigOperators ENNReal
noncomputable section

local instance sourceKPCuspHaarCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sourceKPCuspHaarCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "E" => mixedEmbedding.mixedSpace K

local notation "Q" => SourceKPCuspPrincipalQuotient K d
local instance sourceKPCuspAnisotropicQuotientMeasurable : MeasurableSpace Q := borel Q
local instance sourceKPCuspAnisotropicQuotientBorel : BorelSpace Q := ⟨rfl⟩

def sourceKPCuspPhysicalDirection (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K) (k : Fin 2) : E :=
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  sourceKPCuspHorizontalDirection K v k

def sourceKPCuspPhysicalGradient (hζ : IsPrimitiveRoot ζ 12) (hd : d ≠ 0)
    (g : I → SourceKPCuspL2 K d) (v : InfinitePlace K) (k : Fin 2) : SourceKPCuspL2 K d :=
  ∑ i, ((sourceKPCuspCoordinates K d hd (sourceKPCuspPhysicalDirection K hζ v k)) i : ℂ) • g i

variable [IsTotallyComplex K] in
 theorem sourceKPCuspPhysicalGradient_coordinates (g : I → SourceKPCuspL2 K d)
    (v : InfinitePlace K) (k : Fin 2) :
    sourceKPCuspL2Coordinates K d hζ hd (sourceKPCuspPhysicalGradient K d hζ hd g v k) =
      sourceKPCuspTorusHorizontalGradient K d hd
        (fun i => sourceKPCuspL2Coordinates K d hζ hd (g i)) v k := by
  simp only [sourceKPCuspPhysicalGradient, sourceKPCuspPhysicalDirection,
    sourceKPCuspTorusHorizontalGradient, unitTorusDerivativeCombination, map_sum, map_smul]

theorem sourceKPCusp_anisotropic_height_poincare
    (f : SourceKPCuspL2 K d) (g : I → SourceKPCuspL2 K d)
    (hfg : SourceKPCuspWeakGradient K d hζ hd f g)
    (hmean : (∫ x, f x ∂sourceKPCuspTraceHaar K d) = 0)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspHorizontalGapConstant K d * (∏ v, y v ^ 2) ^
        (1 / (InfinitePlace.nrComplexPlaces K : ℝ)) * ‖f‖ ^ 2 ≤
      ∑ v, y v ^ 2 * ∑ k : Fin 2, ‖sourceKPCuspPhysicalGradient K d hζ hd g v k‖ ^ 2 := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  have hm : (∫ x, sourceKPCuspL2Coordinates K d hζ hd f x ∂unitTorusHaar I) = 0 :=
    (sourceKPCuspL2Coordinates_integral K d hζ hd f).trans hmean
  have h := sourceKPCuspTorus_anisotropic_height_poincare K d hd
    (sourceKPCuspL2Coordinates K d hζ hd f)
    (fun i => sourceKPCuspL2Coordinates K d hζ hd (g i)) hfg hm y hy
  simpa only [← sourceKPCuspPhysicalGradient_coordinates, LinearIsometryEquiv.norm_map] using h

theorem sourceKPCuspL2_norm_sq_integral (f : SourceKPCuspL2 K d) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂sourceKPCuspTraceHaar K d := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq]


def sourceKPCuspPhysicalDerivativeC (hζ : IsPrimitiveRoot ζ 12) (hd : d ≠ 0)
    (g : I → C(Q, ℂ)) (v : InfinitePlace K) (k : Fin 2) : C(Q, ℂ) :=
  ∑ i, ((sourceKPCuspCoordinates K d hd (sourceKPCuspPhysicalDirection K hζ v k)) i : ℂ) • g i

theorem sourceKPCuspPhysicalGradient_continuousL2
    (g : I → C(Q, ℂ)) (v : InfinitePlace K) (k : Fin 2) :
    sourceKPCuspPhysicalGradient K d hζ hd
      (fun i => sourceKPCuspContinuousL2 K d hζ hd (g i)) v k =
      sourceKPCuspContinuousL2 K d hζ hd (sourceKPCuspPhysicalDerivativeC K d hζ hd g v k) := by
  have hcomp : sourceKPCuspCoordinatePullback K d hd (sourceKPCuspPhysicalDerivativeC K d hζ hd g v k) =
      ∑ i, ((sourceKPCuspCoordinates K d hd (sourceKPCuspPhysicalDirection K hζ v k)) i : ℂ) •
        sourceKPCuspCoordinatePullback K d hd (g i) := by
    ext x
    simp [sourceKPCuspPhysicalDerivativeC, sourceKPCuspCoordinatePullback]
  apply (sourceKPCuspL2Coordinates K d hζ hd).injective
  rw [sourceKPCuspL2Coordinates_continuous, hcomp, map_sum]
  simp only [sourceKPCuspPhysicalGradient, map_sum, map_smul, sourceKPCuspL2Coordinates_continuous]

include hζ hd in
 private theorem sourceKPCusp_continuous_norm_sq (f : C(Q, ℂ)) :
    ‖sourceKPCuspContinuousL2 K d hζ hd f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂sourceKPCuspTraceHaar K d := by
  rw [sourceKPCuspL2_norm_sq_integral K d]
  apply integral_congr_ae
  filter_upwards [sourceKPCuspContinuousL2_coe K d hζ hd f] with x hx
  rw [hx]

theorem sourceKPCusp_directional_anisotropic_poincare
    (f : C(Q, ℂ)) (g : I → C(Q, ℂ))
    (hfg : SourceKPCuspDirectionalDerivative K d hd f g)
    (hmean : (∫ x, f x ∂sourceKPCuspTraceHaar K d) = 0)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspHorizontalGapConstant K d * (∏ v, y v ^ 2) ^
        (1 / (InfinitePlace.nrComplexPlaces K : ℝ)) * (∫ x, ‖f x‖ ^ 2 ∂sourceKPCuspTraceHaar K d) ≤
      ∑ v, y v ^ 2 * ∑ k : Fin 2,
        ∫ x, ‖sourceKPCuspPhysicalDerivativeC K d hζ hd g v k x‖ ^ 2 ∂sourceKPCuspTraceHaar K d := by
  have hm : (∫ x, sourceKPCuspContinuousL2 K d hζ hd f x ∂sourceKPCuspTraceHaar K d) = 0 :=
    (integral_congr_ae (sourceKPCuspContinuousL2_coe K d hζ hd f)).trans hmean
  have h := sourceKPCusp_anisotropic_height_poincare K d hζ hd
    (sourceKPCuspContinuousL2 K d hζ hd f) (fun i => sourceKPCuspContinuousL2 K d hζ hd (g i))
    (sourceKPCuspWeakGradient_of_directionalDerivative K d hζ hd f g hfg) hm y hy
  simpa only [sourceKPCuspPhysicalGradient_continuousL2, sourceKPCusp_continuous_norm_sq] using h

theorem sourceKPCuspPhysicalDerivativeC_hasDerivAt
    (f : C(Q, ℂ)) (g : I → C(Q, ℂ))
    (hfg : SourceKPCuspDirectionalDerivative K d hd f g)
    (hF : Differentiable ℝ (fun x : E => f (sourceKPCuspArchQuotientMap K d x)))
    (v : InfinitePlace K) (k : Fin 2) (x : E) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (sourceKPCuspArchQuotientMap K d
      (x + u • sourceKPCuspPhysicalDirection K hζ v k)))
      (sourceKPCuspPhysicalDerivativeC K d hζ hd g v k
        (sourceKPCuspArchQuotientMap K d (x + t • sourceKPCuspPhysicalDirection K hζ v k))) t := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  exact sourceKPCuspCartesianDerivativeC_hasDerivAt K d hd f g hfg hF v k x t

end
end ArtinMatthews
