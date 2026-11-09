module

public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceKPArchComponentBorel


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchComponentEmbedding_measurableEmbedding (b : SourceKPFiniteLevelFiber K hζ) :
    MeasurableEmbedding (sourceKPArchComponentEmbedding K hζ b) :=
  (sourceKPArchComponentEmbedding_isOpenEmbedding K hζ b).measurableEmbedding

instance sourceKPAutomorphicComponentMeasure_sigmaFinite
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] [SigmaFinite μ]
    (i : SourceKPFiniteOrbit K hζ) :
    SigmaFinite (sourceKPAutomorphicComponentMeasure K hζ μ i) :=
  (sourceKPArchComponentEmbedding_measurableEmbedding K hζ _).sigmaFinite_map

instance sourceKPAutomorphicMeasure_sigmaFinite
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] [SigmaFinite μ] :
    SigmaFinite (sourceKPAutomorphicMeasure K hζ μ) := by
  unfold sourceKPAutomorphicMeasure
  infer_instance

end
end ArtinMatthews
