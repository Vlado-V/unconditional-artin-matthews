module

public import ArtinMatthews.QuotientSectionMeasure
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Topology MeasureTheory
noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
variable (K : Subgroup G) [MeasurableSpace (G ⧸ K)] [BorelSpace (G ⧸ K)]
variable (sectionMap : G ⧸ K → G)
variable (sectionRightInverse : ∀ q : G ⧸ K, QuotientGroup.mk (sectionMap q) = q)
variable (continuousSection : Continuous sectionMap)
variable (baseMeasure : Measure (G ⧸ K)) (compactMeasure : Measure K)
include sectionRightInverse continuousSection

theorem quotientSectionMeasure_isHaar
    [SFinite baseMeasure] [SFinite compactMeasure]
    [IsFiniteMeasureOnCompacts baseMeasure] [baseMeasure.IsOpenPosMeasure]
    [compactMeasure.IsHaarMeasure]
    (baseInvariant : ∀ g : G,
      MeasurePreserving (fun q : G ⧸ K => g • q) baseMeasure baseMeasure) :
    (quotientSectionMeasure K sectionMap baseMeasure compactMeasure).IsHaarMeasure := by
  have leftInvariant :
      (quotientSectionMeasure K sectionMap baseMeasure compactMeasure).IsMulLeftInvariant :=
    ⟨fun g => (quotientSectionMeasure_left_preserving K sectionMap
      sectionRightInverse continuousSection baseMeasure compactMeasure g (baseInvariant g)).map_eq⟩
  have openPositive :
      (quotientSectionMeasure K sectionMap baseMeasure compactMeasure).IsOpenPosMeasure := by
    change (Measure.map (quotientSectionFrameInverse K sectionMap)
      (baseMeasure.prod compactMeasure)).IsOpenPosMeasure
    exact (quotientSectionFrameInverse_continuous K sectionMap continuousSection).isOpenPosMeasure_map
      (μ := baseMeasure.prod compactMeasure)
      ((quotientSectionFrameHomeomorph K sectionMap sectionRightInverse continuousSection).symm.surjective)
  have finiteOnCompacts : IsFiniteMeasureOnCompacts
      (quotientSectionMeasure K sectionMap baseMeasure compactMeasure) := by
    constructor
    intro C hC
    change Measure.map (quotientSectionFrameInverse K sectionMap) (baseMeasure.prod compactMeasure) C < ⊤
    rw [Measure.map_apply
      (quotientSectionFrameInverse_continuous K sectionMap continuousSection).measurable
      hC.isClosed.measurableSet]
    have heq : quotientSectionFrameInverse K sectionMap ⁻¹' C =
        quotientSectionFrame K sectionMap sectionRightInverse '' C := by
      ext p
      constructor
      · intro hp
        exact ⟨quotientSectionFrameInverse K sectionMap p,hp,
          quotientSectionFrame_frameInverse K sectionMap sectionRightInverse p⟩
      · rintro ⟨g,hg,rfl⟩
        change quotientSectionFrameInverse K sectionMap
          (quotientSectionFrame K sectionMap sectionRightInverse g) ∈ C
        simpa only [quotientSectionFrameInverse_frame] using hg
    rw [heq]
    exact (hC.image (quotientSectionFrame_continuous K sectionMap sectionRightInverse
      continuousSection)).measure_lt_top
  exact {
    toIsMulLeftInvariant := leftInvariant
    toIsOpenPosMeasure := openPositive
    toIsFiniteMeasureOnCompacts := finiteOnCompacts }

end
end ArtinMatthews
