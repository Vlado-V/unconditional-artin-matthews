module

public import ArtinMatthews.SourceKPFiniteChartCoordinates
public import ArtinMatthews.SourceKPFiniteChartL2Lift


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

omit [NumberField K] in
theorem sourceKPArchUpperEuclideanMap_injective :
    Function.Injective (sourceKPArchUpperEuclideanMap K) :=
  Function.LeftInverse.injective (sourceKPArchUpperEuclideanMap_left_inverse K)

theorem sourceKPFiniteChartCoordinates_preimage
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    (sourceKPArchUpperEuclideanMap K) ⁻¹' sourceKPFiniteChartCoordinateDomain K hζ b p =
      (sourceKPUpperFiniteChart K hζ b p).domain := by
  unfold sourceKPFiniteChartCoordinateDomain
  exact Set.preimage_image_eq _ (sourceKPArchUpperEuclideanMap_injective K)

/-- The unweighted local hyperbolic measure is the actual restricted coordinate measure. -/
theorem sourceKPFiniteChartCoordinates_measurePreserving
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    MeasurePreserving
      (fun x : (sourceKPUpperFiniteChart K hζ b p).domain =>
        sourceKPArchUpperEuclideanMap K x.val)
      (sourceFiniteChartDomainMeasure (sourceKPUpperFiniteChart K hζ b p)
        (sourceKPArchHyperbolicMeasure K))
      ((productVolume (InfinitePlace K)).restrict (sourceKPFiniteChartCoordinateDomain K hζ b p)) := by
  have hm := (sourceKPArchUpperEuclideanMap_preserving K).measurable
  refine ⟨hm.comp measurable_subtype_coe, ?_⟩
  change Measure.map (sourceKPArchUpperEuclideanMap K ∘ Subtype.val)
    ((sourceKPArchHyperbolicMeasure K).comap Subtype.val) = _
  rw [← Measure.map_map hm measurable_subtype_coe]
  have hs := map_comap_subtype_coe
    (s := ((sourceKPUpperFiniteChart K hζ b p).domain : Set (SourceKPArchUpperHalfSpace K)))
    (sourceKPUpperFiniteChart K hζ b p).isOpen_domain.measurableSet (sourceKPArchHyperbolicMeasure K)
  trans Measure.map (sourceKPArchUpperEuclideanMap K)
    ((sourceKPArchHyperbolicMeasure K).restrict (sourceKPUpperFiniteChart K hζ b p).domain)
  · exact congrArg (Measure.map (sourceKPArchUpperEuclideanMap K)) hs
  unfold productVolume
  rw [← (sourceKPArchUpperEuclideanMap_preserving K).map_eq,
    Measure.restrict_map hm (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet,
    sourceKPFiniteChartCoordinates_preimage]

end
end ArtinMatthews
