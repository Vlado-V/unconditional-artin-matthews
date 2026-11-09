module

public import ArtinMatthews.SourceKPAutomorphicComponentTopology
public import ArtinMatthews.SourceKPArchComponentRegularity


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
