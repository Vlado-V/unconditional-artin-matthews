module

public import ArtinMatthews.SourceKPAutomorphicCompactMeasure
public import ArtinMatthews.SourceKPAutomorphicMeasureRegularity
public import ArtinMatthews.SourceKPArchHaar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAutomorphicCompactHaar_finiteOnCompacts :
    IsFiniteMeasureOnCompacts
      (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) := by
  infer_instance

theorem sourceKPAutomorphicCompactHaar_sigmaFinite :
    SigmaFinite (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) := by
  infer_instance

theorem sourceKPAutomorphicCompactHaar_openPositive :
    (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)).IsOpenPosMeasure := by
  infer_instance

end
end ArtinMatthews
