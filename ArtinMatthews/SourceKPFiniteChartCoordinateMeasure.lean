module

public import ArtinMatthews.SourceKPFiniteChartCoordinates
public import ArtinMatthews.FiniteIsotropyChartMeasure
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

namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

omit [NumberField K] in
theorem sourceKPArchUpperEuclideanMap_injective :
    Function.Injective (sourceKPArchUpperEuclideanMap K) :=
  Function.LeftInverse.injective (sourceKPArchUpperEuclideanMap_left_inverse K)

theorem sourceKPFiniteChartCoordinates_preimage
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    (sourceKPArchUpperEuclideanMap K) ⁻¹' sourceKPFiniteChartCoordinateDomain K hζ b p =
      (sourceKPUpperFiniteChart K hζ b p).domain := by
  unfold sourceKPFiniteChartCoordinateDomain
  exact Set.preimage_image_eq _ (sourceKPArchUpperEuclideanMap_injective K)

/-- The unweighted local hyperbolic measure is the actual restricted coordinate measure. -/
theorem sourceKPFiniteChartCoordinates_measurePreserving
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    MeasurePreserving
      (fun x : (sourceKPUpperFiniteChart K hζ b p).domain =>
        sourceKPArchUpperEuclideanMap K x.val)
      (sourceFiniteChartDomainMeasure (sourceKPUpperFiniteChart K hζ b p)
        (sourceKPArchHyperbolicMeasure K))
      ((productVolume (InfinitePlace K)).restrict (sourceKPFiniteChartCoordinateDomain K hζ b p)) := by
  have hm := (sourceKPArchUpperEuclideanMap_preserving K).measurable
  refine ⟨hm.comp measurable_subtype_coe, ?_⟩
  change Measure.map (sourceKPArchUpperEuclideanMap K ∘ Subtype.val)
    ((sourceKPArchHyperbolicMeasure K).comap Subtype.val) = _
  rw [← Measure.map_map hm measurable_subtype_coe]
  have hs := map_comap_subtype_coe
    (s := ((sourceKPUpperFiniteChart K hζ b p).domain : Set (SourceKPArchUpperHalfSpace K)))
    (sourceKPUpperFiniteChart K hζ b p).isOpen_domain.measurableSet (sourceKPArchHyperbolicMeasure K)
  trans Measure.map (sourceKPArchUpperEuclideanMap K)
    ((sourceKPArchHyperbolicMeasure K).restrict (sourceKPUpperFiniteChart K hζ b p).domain)
  · exact congrArg (Measure.map (sourceKPArchUpperEuclideanMap K)) hs
  unfold productVolume
  rw [← (sourceKPArchUpperEuclideanMap_preserving K).map_eq,
    Measure.restrict_map hm (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet,
    sourceKPFiniteChartCoordinates_preimage]

end
end ArtinMatthews
