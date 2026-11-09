module

public import ArtinMatthews.QuotientSectionMeasure


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Topology MeasureTheory
noncomputable section

section Algebra
variable {G : Type*} [Group G] (K : Subgroup G) (sectionMap : G ⧸ K → G)
variable (sectionRightInverse : ∀ q : G ⧸ K, QuotientGroup.mk (sectionMap q) = q)

theorem quotientSectionFrame_mul_right (g : G) (k : K) :
    quotientSectionFrame K sectionMap sectionRightInverse (g*k.val) =
      ((quotientSectionFrame K sectionMap sectionRightInverse g).1,
        (quotientSectionFrame K sectionMap sectionRightInverse g).2 * k) := by
  have hq : (QuotientGroup.mk (g*k.val) : G ⧸ K) = QuotientGroup.mk g :=
    QuotientGroup.mk_mul_of_mem g k.property
  apply Prod.ext
  · exact hq
  · apply Subtype.ext
    change (sectionMap (QuotientGroup.mk (g*k.val)))⁻¹ * (g*k.val) =
      ((sectionMap (QuotientGroup.mk g))⁻¹ * g) * k.val
    rw [hq,mul_assoc]
end Algebra

section Measure
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (K : Subgroup G) [MeasurableSpace (G ⧸ K)] [BorelSpace (G ⧸ K)]
variable (sectionMap : G ⧸ K → G)
variable (sectionRightInverse : ∀ q : G ⧸ K, QuotientGroup.mk (sectionMap q) = q)
variable (continuousSection : Continuous sectionMap)
variable (baseMeasure : Measure (G ⧸ K)) (compactMeasure : Measure K)
include sectionRightInverse continuousSection

theorem quotientSectionMeasure_right_preserving
    [SFinite baseMeasure] [SFinite compactMeasure] [compactMeasure.IsMulRightInvariant]
    (k : K) :
    MeasurePreserving (fun x : G => x*k.val)
      (quotientSectionMeasure K sectionMap baseMeasure compactMeasure)
      (quotientSectionMeasure K sectionMap baseMeasure compactMeasure) := by
  let transform : (G ⧸ K) × K → (G ⧸ K) × K := Prod.map id (fun h => h*k)
  have transformPreserving : MeasurePreserving transform
      (baseMeasure.prod compactMeasure) (baseMeasure.prod compactMeasure) :=
    (MeasurePreserving.id baseMeasure).prod (measurePreserving_mul_right compactMeasure k)
  have assembled := (quotientSectionFrameInverse_measurePreserving K sectionMap continuousSection
    baseMeasure compactMeasure).comp (transformPreserving.comp
      (quotientSectionFrame_measurePreserving K sectionMap sectionRightInverse continuousSection
        baseMeasure compactMeasure))
  convert assembled using 1
  funext x
  change x*k.val = quotientSectionFrameInverse K sectionMap
    (transform (quotientSectionFrame K sectionMap sectionRightInverse x))
  rw [show transform (quotientSectionFrame K sectionMap sectionRightInverse x) =
    quotientSectionFrame K sectionMap sectionRightInverse (x*k.val) from
      (quotientSectionFrame_mul_right K sectionMap sectionRightInverse x k).symm]
  exact (quotientSectionFrameInverse_frame K sectionMap sectionRightInverse (x*k.val)).symm
end Measure

end
end ArtinMatthews
