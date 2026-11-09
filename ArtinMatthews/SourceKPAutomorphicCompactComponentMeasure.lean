module

public import ArtinMatthews.SourceKPAutomorphicMeasureChoice
public import ArtinMatthews.SourceKPAutomorphicComponentMeasure
public import ArtinMatthews.SourceKPAutomorphicL2


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAutomorphicCompactComponentSet (i : SourceKPFiniteOrbit K hζ) :
    Set (SourceKPAutomorphicCompactLevel K hζ) :=
  (sourceKPAutomorphicCompactFiniteOrbit K hζ) ⁻¹' {i}

theorem sourceKPAutomorphicCompactComponentSet_measurable (i : SourceKPFiniteOrbit K hζ) :
    MeasurableSet (sourceKPAutomorphicCompactComponentSet K hζ i) :=
  ((isOpen_discrete ({i} : Set (SourceKPFiniteOrbit K hζ))).preimage
    (sourceKPAutomorphicCompactFiniteOrbit_continuous K hζ)).measurableSet

theorem sourceKPAutomorphicCompactComponentSet_preimage (i : SourceKPFiniteOrbit K hζ) :
    (sourceKPAutomorphicCompactMk K hζ) ⁻¹' sourceKPAutomorphicCompactComponentSet K hζ i =
      sourceKPAutomorphicComponentSet K hζ i := rfl

theorem sourceKPAutomorphicCompactMeasure_restrict_component
    (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    (sourceKPAutomorphicCompactMeasure K hζ μ).restrict
        (sourceKPAutomorphicCompactComponentSet K hζ (sourceKPFiniteOrbitMk K hζ b)) =
      Measure.map (fun q : SourceKPArchComponentQuotient K hζ b =>
        sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentEmbedding K hζ b q))
        (sourceKPArchComponentQuotientMeasure K hζ b μ) := by
  unfold sourceKPAutomorphicCompactMeasure
  rw [Measure.restrict_map (sourceKPAutomorphicCompactMk_measurable K hζ)
      (sourceKPAutomorphicCompactComponentSet_measurable K hζ _),
    sourceKPAutomorphicCompactComponentSet_preimage,
    sourceKPAutomorphicMeasure_restrict_component,
    ← sourceKPArchComponentPushMeasure_eq_component K hζ b μ]
  exact Measure.map_map (sourceKPAutomorphicCompactMk_measurable K hζ)
    (sourceKPArchComponentEmbedding_measurable K hζ b)

end
end ArtinMatthews
