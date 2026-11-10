module

public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPFiniteChartCoordinates
public import ArtinMatthews.SourceKPFiniteChartCoordinateMeasure
public import ArtinMatthews.SourceKPGlobalChartMeasure
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
open scoped NumberField MatrixGroups AdeleRing Topology Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFiniteChart_integral
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (F : SourceKPAutomorphicCompactLevel K hζ → ℝ) (hF : Measurable F) :
    (∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
      F (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x))
        ∂productVolume (InfinitePlace K)) =
      (Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ) *
        ∫ y in Set.range (sourceKPFiniteChartProjection K hζ b p), F y
          ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
  let c := sourceKPUpperFiniteChart K hζ b p
  let μD := sourceFiniteChartDomainMeasure c (sourceKPArchHyperbolicMeasure K)
  let π := sourceKPFiniteChartProjection K hζ b p
  let n : ℝ := Nat.card (SourceKPFiniteChartStabilizer K hζ b p)
  let L : ProductSpace (InfinitePlace K) → ℝ :=
    fun x => F (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x))
  have hL : Measurable L := hF.comp
    ((sourceKPUpperToCompact_continuous K hζ b).measurable.comp
      (sourceKPArchEuclideanUpperMap_preserving K).measurable)
  have hcoord : (∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
      L x ∂productVolume (InfinitePlace K)) = ∫ x : c.domain, F (π x) ∂μD := by
    have hm := sourceKPFiniteChartCoordinates_measurePreserving K hζ b p
    calc
      _ = ∫ x, L x ∂Measure.map
          (fun x : c.domain => sourceKPArchUpperEuclideanMap K x.val) μD := by rw [hm.map_eq]
      _ = ∫ x : c.domain, L (sourceKPArchUpperEuclideanMap K x.val) ∂μD :=
        integral_map hm.measurable.aemeasurable hL.aestronglyMeasurable
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [L, π, sourceKPFiniteChartProjection]
        rw [sourceKPArchUpperEuclideanMap_left_inverse]
  have hquot : (∫ y in Set.range π, F y
      ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) =
      n⁻¹ * ∫ x : c.domain, F (π x) ∂μD := by
    have hm := sourceKPFiniteChartProjection_measurePreserving K hζ b p
    calc
      _ = ∫ y, F y ∂Measure.map π
          ((Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ≥0∞)⁻¹ • μD) := by
        rw [hm.map_eq]
      _ = ∫ x : c.domain, F (π x)
          ∂((Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ≥0∞)⁻¹ • μD) :=
        integral_map hm.measurable.aemeasurable hF.aestronglyMeasurable
      _ = _ := by
        rw [integral_smul_measure]
        simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, n]
  have hn : n ≠ 0 := by
    dsimp only [n]
    exact_mod_cast (Nat.card_pos.ne' : Nat.card (SourceKPFiniteChartStabilizer K hζ b p) ≠ 0)
  change (∫ x in sourceKPFiniteChartCoordinateDomain K hζ b p,
    L x ∂productVolume (InfinitePlace K)) = n * _
  rw [hcoord, hquot]
  field_simp [hn]

theorem sourceKPFiniteChart_integrable_pullback
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (F : SourceKPAutomorphicCompactLevel K hζ → ℝ) (hF : Measurable F)
    (hI : Integrable F (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ))) :
    IntegrableOn (fun x => F (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x)))
      (sourceKPFiniteChartCoordinateDomain K hζ b p) (productVolume (InfinitePlace K)) := by
  let c := sourceKPUpperFiniteChart K hζ b p
  let μD := sourceFiniteChartDomainMeasure c (sourceKPArchHyperbolicMeasure K)
  let π := sourceKPFiniteChartProjection K hζ b p
  let L : ProductSpace (InfinitePlace K) → ℝ :=
    fun x => F (sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K x))
  have hL : Measurable L := hF.comp
    ((sourceKPUpperToCompact_continuous K hζ b).measurable.comp
      (sourceKPArchEuclideanUpperMap_preserving K).measurable)
  have hweighted : Integrable (F ∘ π)
      ((Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ≥0∞)⁻¹ • μD) :=
    (sourceKPFiniteChartProjection_measurePreserving K hζ b p).integrable_comp_of_integrable
      hI.integrableOn
  have hn : (Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos.ne' : Nat.card (SourceKPFiniteChartStabilizer K hζ b p) ≠ 0)
  have hsub : Integrable (F ∘ π) μD :=
    (integrable_inv_smul_measure hn (ENNReal.natCast_ne_top _)).mp hweighted
  have heq : (F ∘ π) = L ∘ (fun x : c.domain => sourceKPArchUpperEuclideanMap K x.val) := by
    funext x
    dsimp only [Function.comp_def, L, π, sourceKPFiniteChartProjection]
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
  rw [heq] at hsub
  exact (sourceKPFiniteChartCoordinates_measurePreserving K hζ b p).integrable_comp
    hL.aestronglyMeasurable |>.mp hsub

end
end ArtinMatthews
