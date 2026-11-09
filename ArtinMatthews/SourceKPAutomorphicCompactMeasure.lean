module

public import ArtinMatthews.SourceKPAutomorphicCompactTopology
public import ArtinMatthews.SourceKPAutomorphicL2
public import Mathlib.MeasureTheory.Measure.OpenPos


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPAutomorphicCompactMeasure_finiteOnCompacts
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [IsFiniteMeasureOnCompacts (sourceKPAutomorphicMeasure K hζ μ)] :
    IsFiniteMeasureOnCompacts (sourceKPAutomorphicCompactMeasure K hζ μ) where
  lt_top_of_isCompact C hC := by
    rw [sourceKPAutomorphicCompactMeasure,
      Measure.map_apply (sourceKPAutomorphicCompactMk_measurable K hζ) hC.isClosed.measurableSet]
    exact (sourceKPAutomorphicCompactMk_isCompact_preimage K hζ hC).measure_lt_top

instance sourceKPAutomorphicCompactMeasure_sigmaFinite
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [IsFiniteMeasureOnCompacts (sourceKPAutomorphicMeasure K hζ μ)] :
    SigmaFinite (sourceKPAutomorphicCompactMeasure K hζ μ) := by
  infer_instance

instance sourceKPAutomorphicCompactMeasure_openPositive
    (μ : Measure (PGL(2, InfiniteAdeleRing K)))
    [(sourceKPAutomorphicMeasure K hζ μ).IsOpenPosMeasure] :
    (sourceKPAutomorphicCompactMeasure K hζ μ).IsOpenPosMeasure :=
  (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous.isOpenPosMeasure_map
    (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).surjective

end
end ArtinMatthews
