module

public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPCompactCoreEnergy
public import ArtinMatthews.SourceKPFiniteChartCoordinates
public import ArtinMatthews.SourceKPCompactCoreMassNorm
public import ArtinMatthews.SourceKPCompactEnergyRegularity
public import ArtinMatthews.SourceKPFiniteChartIntegration
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

theorem sourceKPCompactChartPullback_ae
    (F : SourceKPAutomorphicCompactLevel K hζ → ℂ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    sourceKPCompactChartPullback K hζ F b =ᵐ[
      (productVolume (InfinitePlace K)).restrict (sourceKPFiniteChartCoordinateDomain K hζ b p)]
      (fun x => F (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x))) := by
  filter_upwards [ae_restrict_mem (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet]
    with x hx
  exact if_pos (sourceKPFiniteChartCoordinateDomain_upper K hζ b p hx)

theorem sourceKPCompactChartEnergy_ae (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    productGradientEnergy (sourceKPCompactChartPullback K hζ f.val b) =ᵐ[
      (productVolume (InfinitePlace K)).restrict (sourceKPFiniteChartCoordinateDomain K hζ b p)]
      (fun x => sourceKPCompactCoreEnergy K hζ f
        (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x))) := by
  filter_upwards [ae_restrict_mem (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet]
    with x hx
  have hpos := sourceKPFiniteChartCoordinateDomain_upper K hζ b p hx
  have he := sourceKPCompactCoreEnergy_chart K hζ f b (sourceKPArchEuclideanUpperMap K x)
  rw [sourceKPArchUpperEuclideanMap_right_inverse K x (fun v => hpos v (Set.mem_univ v))] at he
  exact he.symm

theorem sourceKPCompactChart_mass_integrable (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    IntegrableOn (fun x => ‖sourceKPCompactChartPullback K hζ f.val b x‖ ^ 2)
      (sourceKPFiniteChartCoordinateDomain K hζ b p) (productVolume (InfinitePlace K)) := by
  have hd := sourceKPFiniteChart_integrable_pullback K hζ b p
    (fun y => ‖f.val y‖ ^ 2) (f.prop.1.measurable.norm.pow_const 2)
    (sourceKPCompactCore_norm_sq_integrable K hζ f)
  apply hd.congr
  filter_upwards [sourceKPCompactChartPullback_ae K hζ f.val b p] with x hx
  rw [hx]

theorem sourceKPCompactChart_energy_integrable (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    IntegrableOn (productGradientEnergy (sourceKPCompactChartPullback K hζ f.val b))
      (sourceKPFiniteChartCoordinateDomain K hζ b p) (productVolume (InfinitePlace K)) := by
  have hd := sourceKPFiniteChart_integrable_pullback K hζ b p
    (sourceKPCompactCoreEnergy K hζ f) (sourceKPCompactCoreEnergy_continuous K hζ f).measurable
    (sourceKPCompactCoreEnergy_integrable K hζ f)
  exact hd.congr (sourceKPCompactChartEnergy_ae K hζ f b p).symm

theorem sourceKPCompactChart_mass_integral (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    (∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
      ‖sourceKPCompactChartPullback K hζ f.val b x‖ ^ 2 ∂productVolume (InfinitePlace K)) =
      (Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ) *
        ∫ y in Set.range (sourceKPFiniteChartProjection K hζ b p), ‖f.val y‖ ^ 2
          ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
  calc
    _ = ∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
        ‖f.val (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x))‖ ^ 2
          ∂productVolume (InfinitePlace K) := by
      apply integral_congr_ae
      filter_upwards [sourceKPCompactChartPullback_ae K hζ f.val b p] with x hx
      rw [hx]
    _ = _ := sourceKPFiniteChart_integral K hζ b p
      (fun y => ‖f.val y‖ ^ 2) (f.prop.1.measurable.norm.pow_const 2)

theorem sourceKPCompactChart_energy_integral (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    (∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
      productGradientEnergy (sourceKPCompactChartPullback K hζ f.val b) x
        ∂productVolume (InfinitePlace K)) =
      (Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ) *
        ∫ y in Set.range (sourceKPFiniteChartProjection K hζ b p), sourceKPCompactCoreEnergy K hζ f y
          ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
  calc
    _ = ∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
        sourceKPCompactCoreEnergy K hζ f
          (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x))
          ∂productVolume (InfinitePlace K) :=
      integral_congr_ae (sourceKPCompactChartEnergy_ae K hζ f b p)
    _ = _ := sourceKPFiniteChart_integral K hζ b p
      (sourceKPCompactCoreEnergy K hζ f) (sourceKPCompactCoreEnergy_continuous K hζ f).measurable

end
end ArtinMatthews
