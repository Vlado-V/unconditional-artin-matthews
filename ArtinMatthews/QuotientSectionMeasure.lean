module

public import ArtinMatthews.QuotientSectionCocycle
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Topology MeasureTheory
noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (K : Subgroup G) [MeasurableSpace (G ⧸ K)] [BorelSpace (G ⧸ K)]
variable (sectionMap : G ⧸ K → G)
variable (sectionRightInverse : ∀ q : G ⧸ K, QuotientGroup.mk (sectionMap q) = q)
variable (continuousSection : Continuous sectionMap)
variable (baseMeasure : Measure (G ⧸ K)) (compactMeasure : Measure K)

def quotientSectionMeasure : Measure G :=
  Measure.map (quotientSectionFrameInverse K sectionMap) (baseMeasure.prod compactMeasure)

include continuousSection in
theorem quotientSectionFrameInverse_measurePreserving :
    MeasurePreserving (quotientSectionFrameInverse K sectionMap)
      (baseMeasure.prod compactMeasure) (quotientSectionMeasure K sectionMap baseMeasure compactMeasure) :=
  ⟨(quotientSectionFrameInverse_continuous K sectionMap continuousSection).measurable,rfl⟩

include continuousSection in
theorem quotientSectionFrame_measurePreserving :
    MeasurePreserving (quotientSectionFrame K sectionMap sectionRightInverse)
      (quotientSectionMeasure K sectionMap baseMeasure compactMeasure) (baseMeasure.prod compactMeasure) := by
  refine ⟨(quotientSectionFrame_continuous K sectionMap sectionRightInverse continuousSection).measurable,?_⟩
  rw [quotientSectionMeasure,Measure.map_map
    (quotientSectionFrame_continuous K sectionMap sectionRightInverse continuousSection).measurable
    (quotientSectionFrameInverse_continuous K sectionMap continuousSection).measurable]
  have he : (quotientSectionFrame K sectionMap sectionRightInverse ∘
      quotientSectionFrameInverse K sectionMap) = id := by
    funext p
    exact quotientSectionFrame_frameInverse K sectionMap sectionRightInverse p
  rw [he,Measure.map_id]

include sectionRightInverse continuousSection in
theorem quotientSectionMeasure_left_preserving
    [SFinite baseMeasure] [SFinite compactMeasure] [compactMeasure.IsMulLeftInvariant]
    (g : G) (baseInvariant : MeasurePreserving (fun q : G ⧸ K => g • q) baseMeasure baseMeasure) :
    MeasurePreserving (fun x : G => g*x)
      (quotientSectionMeasure K sectionMap baseMeasure compactMeasure)
      (quotientSectionMeasure K sectionMap baseMeasure compactMeasure) := by
  let transform : (G ⧸ K) × K → (G ⧸ K) × K := fun p =>
    (g • p.1, quotientSectionCocycle K sectionMap sectionRightInverse g p.1 * p.2)
  have measurableFiber : Measurable (fun p : (G ⧸ K) × K =>
      quotientSectionCocycle K sectionMap sectionRightInverse g p.1 * p.2) :=
    (((quotientSectionCocycle_continuous K sectionMap sectionRightInverse continuousSection g).comp
      continuous_fst).mul continuous_snd).measurable
  have transformPreserving : MeasurePreserving transform
      (baseMeasure.prod compactMeasure) (baseMeasure.prod compactMeasure) :=
    baseInvariant.skew_product measurableFiber (Filter.Eventually.of_forall (fun q =>
      map_mul_left_eq_self compactMeasure (quotientSectionCocycle K sectionMap sectionRightInverse g q)))
  have assembled := (quotientSectionFrameInverse_measurePreserving K sectionMap continuousSection
    baseMeasure compactMeasure).comp (transformPreserving.comp
      (quotientSectionFrame_measurePreserving K sectionMap sectionRightInverse continuousSection
        baseMeasure compactMeasure))
  convert assembled using 1
  funext x
  change g*x = quotientSectionFrameInverse K sectionMap
    (transform (quotientSectionFrame K sectionMap sectionRightInverse x))
  rw [show transform (quotientSectionFrame K sectionMap sectionRightInverse x) =
    quotientSectionFrame K sectionMap sectionRightInverse (g*x) from
      (quotientSectionFrame_mul K sectionMap sectionRightInverse g x).symm]
  exact (quotientSectionFrameInverse_frame K sectionMap sectionRightInverse (g*x)).symm

include sectionRightInverse continuousSection in
theorem quotientSectionMeasure_projection [SFinite baseMeasure] [SFinite compactMeasure]
    [IsProbabilityMeasure compactMeasure] :
    MeasurePreserving (QuotientGroup.mk : G → G ⧸ K)
      (quotientSectionMeasure K sectionMap baseMeasure compactMeasure) baseMeasure := by
  have h := (measurePreserving_fst (μ := baseMeasure) (ν := compactMeasure)).comp
    (quotientSectionFrame_measurePreserving K sectionMap sectionRightInverse continuousSection
      baseMeasure compactMeasure)
  exact h

end
end ArtinMatthews
