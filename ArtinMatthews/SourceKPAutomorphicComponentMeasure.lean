module

public import ArtinMatthews.SourceKPAutomorphicMeasure


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAutomorphicComponentSet (i : SourceKPFiniteOrbit K hζ) :
    Set (SourceKPAutomorphicLevel K hζ) :=
  (sourceKPAutomorphicFiniteOrbit K hζ) ⁻¹' {i}

theorem sourceKPAutomorphicComponentSet_measurable (i : SourceKPFiniteOrbit K hζ) :
    MeasurableSet (sourceKPAutomorphicComponentSet K hζ i) :=
  ((isOpen_discrete ({i} : Set (SourceKPFiniteOrbit K hζ))).preimage
    (sourceKPAutomorphicFiniteOrbit_continuous K hζ)).measurableSet

theorem sourceKPAutomorphicFiniteOrbit_embedding (b : SourceKPFiniteLevelFiber K hζ)
    (q : SourceKPArchComponentQuotient K hζ b) :
    sourceKPAutomorphicFiniteOrbit K hζ (sourceKPArchComponentEmbedding K hζ b q) =
      sourceKPFiniteOrbitMk K hζ b := by
  induction q using Quotient.inductionOn with
  | _ a => rfl

theorem sourceKPAutomorphicComponentMeasure_intersection
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) (i j : SourceKPFiniteOrbit K hζ)
    (U : Set (SourceKPAutomorphicLevel K hζ)) (hU : MeasurableSet U) :
    sourceKPAutomorphicComponentMeasure K hζ μ j (U ∩ sourceKPAutomorphicComponentSet K hζ i) =
      if j = i then sourceKPAutomorphicComponentMeasure K hζ μ j U else 0 := by
  classical
  rw [sourceKPAutomorphicComponentMeasure_apply K hζ μ j _
    (hU.inter (sourceKPAutomorphicComponentSet_measurable K hζ i))]
  by_cases hji : j = i
  · rw [ite_eq_left hji,sourceKPAutomorphicComponentMeasure_apply K hζ μ j U hU]
    congr 1
    ext q
    simp [sourceKPAutomorphicComponentSet,sourceKPAutomorphicFiniteOrbit_embedding,
      sourceKPFiniteOrbitRepresentative_spec,hji]
  · rw [ite_eq_right hji]
    have he : (sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ j)) ⁻¹'
        (U ∩ sourceKPAutomorphicComponentSet K hζ i) = ∅ := by
      ext q
      simp [sourceKPAutomorphicComponentSet,sourceKPAutomorphicFiniteOrbit_embedding,
        sourceKPFiniteOrbitRepresentative_spec,hji]
    rw [he,measure_empty]

theorem sourceKPAutomorphicMeasure_restrict_component
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) (i : SourceKPFiniteOrbit K hζ) :
    (sourceKPAutomorphicMeasure K hζ μ).restrict (sourceKPAutomorphicComponentSet K hζ i) =
      sourceKPAutomorphicComponentMeasure K hζ μ i := by
  ext U hU
  rw [Measure.restrict_apply hU,sourceKPAutomorphicMeasure,Measure.sum_apply _
    (hU.inter (sourceKPAutomorphicComponentSet_measurable K hζ i))]
  simp_rw [sourceKPAutomorphicComponentMeasure_intersection K hζ μ _ _ U hU]
  simp

end
end ArtinMatthews
