module

public import ArtinMatthews.QuotientSectionMeasure
public import ArtinMatthews.QuotientSectionRightMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Right-equivariant maps lift base measure transport through a compact frame. -/
namespace ArtinMatthews
open Topology MeasureTheory
open scoped ENNReal
noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
variable (K : Subgroup G) [MeasurableSpace (G ⧸ K)] [BorelSpace (G ⧸ K)]
variable (sectionMap : G ⧸ K → G)
variable (sectionRightInverse : ∀ q : G ⧸ K, QuotientGroup.mk (sectionMap q) = q)
variable (continuousSection : Continuous sectionMap)
variable (μ ν : Measure (G ⧸ K)) (κ : Measure K)

include sectionRightInverse continuousSection in
theorem quotientSectionMeasure_equivariant_transport [SFinite μ] [SFinite κ]
    [κ.IsMulLeftInvariant] (F : G → G) (hF : Continuous F)
    (hFK : ∀ g (k : K), F (g*k.val) = F g*k.val)
    (f : G ⧸ K → G ⧸ K) (hf : MeasurePreserving f μ ν)
    (hbase : ∀ g, QuotientGroup.mk (F g) = f (QuotientGroup.mk g)) :
    MeasurePreserving F (quotientSectionMeasure K sectionMap μ κ)
      (quotientSectionMeasure K sectionMap ν κ) := by
  let fiber : G ⧸ K → K := fun q =>
    (quotientSectionFrame K sectionMap sectionRightInverse (F (sectionMap q))).2
  have hfiber : Continuous fiber :=
    continuous_snd.comp ((quotientSectionFrame_continuous K sectionMap
      sectionRightInverse continuousSection).comp (hF.comp continuousSection))
  let transform : (G ⧸ K) × K → (G ⧸ K) × K := fun p => (f p.1, fiber p.1*p.2)
  have htransform : MeasurePreserving transform (μ.prod κ) (ν.prod κ) :=
    hf.skew_product ((hfiber.comp continuous_fst).mul continuous_snd).measurable
      (Filter.Eventually.of_forall (fun q => map_mul_left_eq_self κ (fiber q)))
  have assembled := (quotientSectionFrameInverse_measurePreserving K sectionMap
    continuousSection ν κ).comp (htransform.comp (quotientSectionFrame_measurePreserving
      K sectionMap sectionRightInverse continuousSection μ κ))
  convert assembled using 1
  funext g
  change F g = quotientSectionFrameInverse K sectionMap
    (transform (quotientSectionFrame K sectionMap sectionRightInverse g))
  have hframe : ∀ p, transform p = quotientSectionFrame K sectionMap sectionRightInverse
      (F (quotientSectionFrameInverse K sectionMap p)) := by
    intro p
    rw [quotientSectionFrameInverse, hFK, quotientSectionFrame_mul_right]
    apply Prod.ext
    · change f p.1 = QuotientGroup.mk (F (sectionMap p.1))
      rw [hbase, sectionRightInverse]
    · rfl
  rw [hframe, quotientSectionFrameInverse_frame, quotientSectionFrameInverse_frame]

include continuousSection in
theorem quotientSectionMeasure_smul [SFinite κ] (c : ℝ≥0∞) :
    quotientSectionMeasure K sectionMap (c • μ) κ =
      c • quotientSectionMeasure K sectionMap μ κ := by
  unfold quotientSectionMeasure
  rw [Measure.prod_smul_left, Measure.map_smul]
  exact (quotientSectionFrameInverse_continuous K sectionMap continuousSection).measurable.aemeasurable

end
end ArtinMatthews
