module

public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceKPArchComponentRegularity
public import ArtinMatthews.SourceKPAutomorphicComponentTopology
public import ArtinMatthews.SourceKPFiniteOrbitFiniteness
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
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchComponentEmbedding_isClosedEmbedding
    (i : SourceKPFiniteOrbit K hζ) :
    IsClosedEmbedding (sourceKPArchComponentEmbedding K hζ
      (sourceKPFiniteOrbitRepresentative K hζ i)) := by
  exact (sourceKPAutomorphicComponentHomeomorph K hζ).isClosedEmbedding.comp
    (Topology.IsClosedEmbedding.sigmaMk (i := i))

instance sourceKPAutomorphicMeasure_finiteOnCompacts
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts (sourceKPAutomorphicMeasure K hζ μ) where
  lt_top_of_isCompact C hC := by
    letI := Fintype.ofFinite (SourceKPFiniteOrbit K hζ)
    rw [sourceKPAutomorphicMeasure_apply K hζ μ C hC.isClosed.measurableSet, tsum_fintype]
    exact ENNReal.sum_lt_top.mpr fun i _ =>
      sourceKPArchComponentQuotientMeasure_finite_on_compacts K hζ
        (sourceKPFiniteOrbitRepresentative K hζ i) μ _
        ((sourceKPArchComponentEmbedding_isClosedEmbedding K hζ i).isCompact_preimage hC)

instance sourceKPAutomorphicMeasure_openPositive
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] :
    (sourceKPAutomorphicMeasure K hζ μ).IsOpenPosMeasure where
  open_pos U hU hne := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨⟨i,q⟩,hqx⟩ := sourceKPAutomorphicComponentUnionMap_surjective K hζ x
    have hpre : (sourceKPArchComponentEmbedding K hζ
        (sourceKPFiniteOrbitRepresentative K hζ i) ⁻¹' U).Nonempty := by
      refine ⟨q,?_⟩
      change sourceKPAutomorphicComponentUnionMap K hζ ⟨i,q⟩ ∈ U
      simpa only [hqx] using hx
    have hpos := (hU.preimage (sourceKPArchComponentEmbedding_continuous K hζ
      (sourceKPFiniteOrbitRepresentative K hζ i))).measure_pos
      (sourceKPArchComponentQuotientMeasure K hζ (sourceKPFiniteOrbitRepresentative K hζ i) μ) hpre
    rw [sourceKPAutomorphicMeasure_apply K hζ μ U hU.measurableSet]
    have hle := ENNReal.le_tsum (f := fun j : SourceKPFiniteOrbit K hζ =>
      sourceKPArchComponentQuotientMeasure K hζ (sourceKPFiniteOrbitRepresentative K hζ j) μ
        ((sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ j)) ⁻¹' U)) i
    exact ne_of_gt (hpos.trans_le hle)

end
end ArtinMatthews
