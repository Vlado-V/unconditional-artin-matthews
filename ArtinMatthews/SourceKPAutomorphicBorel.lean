module

public import ArtinMatthews.SourceKPFiniteOrbit
public import ArtinMatthews.SourceKPArchMeasureTopology


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPAutomorphicLevel_measurableSpace :
    MeasurableSpace (SourceKPAutomorphicLevel K hζ) := borel _

instance sourceKPAutomorphicLevel_borelSpace :
    BorelSpace (SourceKPAutomorphicLevel K hζ) := ⟨rfl⟩

theorem sourceKPArchComponentPoint_measurable (b : SourceKPFiniteLevelFiber K hζ) :
    Measurable (sourceKPArchComponentPoint K hζ b) :=
  (sourceKPArchComponentPoint_continuous K hζ b).measurable

theorem sourceKPArchComponentEmbedding_measurable (b : SourceKPFiniteLevelFiber K hζ) :
    Measurable (sourceKPArchComponentEmbedding K hζ b) := by
  intro U hU
  change MeasurableSet ((Quotient.mk (QuotientGroup.rightRel
    (sourceKPArchComponentSubgroup K hζ b))) ⁻¹'
      ((sourceKPArchComponentEmbedding K hζ b) ⁻¹' U))
  change MeasurableSet ((sourceKPArchComponentPoint K hζ b) ⁻¹' U)
  exact sourceKPArchComponentPoint_measurable K hζ b hU

end
end ArtinMatthews
