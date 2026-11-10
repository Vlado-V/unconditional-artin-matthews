module

public import ArtinMatthews.QuotientSectionMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Topology MeasureTheory
noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (K : Subgroup G) [MeasurableSpace (G ⧸ K)] [BorelSpace (G ⧸ K)]
variable (sectionMap : G ⧸ K → G) (continuousSection : Continuous sectionMap)
variable (baseMeasure : Measure (G ⧸ K)) (compactMeasure : Measure K)
variable [SFinite baseMeasure] [SFinite compactMeasure]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
include continuousSection

theorem quotientSectionMeasure_integral (f : G → E)
    (hf : Integrable f (quotientSectionMeasure K sectionMap baseMeasure compactMeasure)) :
    (∫ g, f g ∂quotientSectionMeasure K sectionMap baseMeasure compactMeasure) =
      ∫ q, ∫ k : K, f (sectionMap q*k.val) ∂compactMeasure ∂baseMeasure := by
  have hi := (integrable_map_measure hf.aestronglyMeasurable
    (quotientSectionFrameInverse_continuous K sectionMap continuousSection).measurable.aemeasurable).mp hf
  calc
    _ = ∫ p : (G ⧸ K) × K, f (quotientSectionFrameInverse K sectionMap p)
        ∂(baseMeasure.prod compactMeasure) :=
      integral_map (quotientSectionFrameInverse_continuous K sectionMap continuousSection).measurable.aemeasurable
        hf.aestronglyMeasurable
    _ = _ := integral_prod _ hi

end
end ArtinMatthews
