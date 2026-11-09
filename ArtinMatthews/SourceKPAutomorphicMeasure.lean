module

public import ArtinMatthews.SourceKPAutomorphicBorel
public import ArtinMatthews.SourceKPArchComponentMeasure
public import ArtinMatthews.SourceKPFiniteOrbitFiniteness


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite-component automorphic measure for a specified
archimedean measure. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFiniteOrbitRepresentative (i : SourceKPFiniteOrbit K hζ) : SourceKPFiniteLevelFiber K hζ :=
  Quotient.out i

theorem sourceKPFiniteOrbitRepresentative_spec (i : SourceKPFiniteOrbit K hζ) :
    sourceKPFiniteOrbitMk K hζ (sourceKPFiniteOrbitRepresentative K hζ i) = i :=
  Quotient.out_eq' i

def sourceKPAutomorphicComponentMeasure
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) (i : SourceKPFiniteOrbit K hζ) :
    Measure (SourceKPAutomorphicLevel K hζ) :=
  Measure.map (sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ i))
    (sourceKPArchComponentQuotientMeasure K hζ (sourceKPFiniteOrbitRepresentative K hζ i) μ)

def sourceKPAutomorphicMeasure (μ : Measure (PGL(2, InfiniteAdeleRing K))) :
    Measure (SourceKPAutomorphicLevel K hζ) :=
  Measure.sum (sourceKPAutomorphicComponentMeasure K hζ μ)

theorem sourceKPAutomorphicComponentMeasure_apply
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) (i : SourceKPFiniteOrbit K hζ)
    (U : Set (SourceKPAutomorphicLevel K hζ)) (hU : MeasurableSet U) :
    sourceKPAutomorphicComponentMeasure K hζ μ i U =
      sourceKPArchComponentQuotientMeasure K hζ (sourceKPFiniteOrbitRepresentative K hζ i) μ
        ((sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ i)) ⁻¹' U) :=
  Measure.map_apply (sourceKPArchComponentEmbedding_measurable K hζ _) hU

theorem sourceKPAutomorphicMeasure_apply
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    (U : Set (SourceKPAutomorphicLevel K hζ)) (hU : MeasurableSet U) :
    sourceKPAutomorphicMeasure K hζ μ U =
      ∑' i : SourceKPFiniteOrbit K hζ,
        sourceKPArchComponentQuotientMeasure K hζ (sourceKPFiniteOrbitRepresentative K hζ i) μ
          ((sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ i)) ⁻¹' U) := by
  rw [sourceKPAutomorphicMeasure,Measure.sum_apply _ hU]
  apply tsum_congr
  intro i
  exact sourceKPAutomorphicComponentMeasure_apply K hζ μ i U hU

end
end ArtinMatthews
