module

public import ArtinMatthews.SourceKPUpperChartMeasure
public import ArtinMatthews.SourceKPCompactCoreCharts
public import ArtinMatthews.SourceKPAutomorphicCompactComponentMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! The actual global compact quotient has reciprocal-stabilizer hyperbolic chart measure. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Topology Set
open scoped NumberField MatrixGroups AdeleRing Classical ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArithmeticUpperMeasure_global_component (b : SourceKPFiniteLevelFiber K hζ) :
    (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)).restrict
      (sourceKPAutomorphicCompactComponentSet K hζ (sourceKPFiniteOrbitMk K hζ b)) =
        (sourceKPArithmeticUpperMeasure K hζ b).map (sourceKPArithmeticUpperComponentMap K hζ b) := by
  rw [sourceKPAutomorphicCompactMeasure_restrict_component]
  unfold sourceKPArithmeticUpperMeasure
  rw [Measure.map_map
    (sourceKPArithmeticUpperComponentMap_isOpenEmbedding K hζ b).measurableEmbedding.measurable
    (sourceKPUpperQuotientProjection_measurable K hζ b)]
  congr 1
  funext q
  exact (sourceKPUpperQuotientProjection_component K hζ b q).symm

theorem sourceKPFiniteChartProjection_measurePreserving (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    MeasurePreserving (sourceKPFiniteChartProjection K hζ b p)
      ((Nat.card (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) p) : ℝ≥0∞)⁻¹ •
        sourceFiniteChartDomainMeasure (sourceKPUpperFiniteChart K hζ b p)
          (sourceKPArchHyperbolicMeasure K))
      ((sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)).restrict
        (Set.range (sourceKPFiniteChartProjection K hζ b p))) := by
  let c := sourceKPUpperFiniteChart K hζ b p
  let f := sourceKPArithmeticUpperComponentMap K hζ b
  let R := Set.range (sourceFiniteChartProjection c)
  have hf : MeasurableEmbedding f :=
    (sourceKPArithmeticUpperComponentMap_isOpenEmbedding K hζ b).measurableEmbedding
  have hp := sourceKPUpperChart_measurePreserving K hζ b p c
  have hRange : Set.range (sourceKPFiniteChartProjection K hζ b p) = f '' R := by
    change Set.range (f ∘ sourceFiniteChartProjection c) = f '' Set.range (sourceFiniteChartProjection c)
    exact Set.range_comp _ _
  have hsubset : f '' R ⊆
      sourceKPAutomorphicCompactComponentSet K hζ (sourceKPFiniteOrbitMk K hζ b) := by
    rintro _ ⟨q, _, rfl⟩
    exact (sourceKPArithmeticUpperComponentHomeomorph K hζ b q).property
  refine ⟨hf.measurable.comp hp.measurable, ?_⟩
  change Measure.map (f ∘ sourceFiniteChartProjection c) _ = _
  rw [← Measure.map_map hf.measurable hp.measurable, hp.map_eq, hRange]
  have hrestrict : ((sourceKPArithmeticUpperMeasure K hζ b).restrict R).map f =
      ((sourceKPArithmeticUpperMeasure K hζ b).map f).restrict (f '' R) := by
    rw [hf.restrict_map, hf.injective.preimage_image]
  rw [hrestrict, ← sourceKPArithmeticUpperMeasure_global_component K hζ b,
    Measure.restrict_restrict_of_subset hsubset]

end
end ArtinMatthews
