module

public import ArtinMatthews.SourceSLocalWholeSplitMeasure
public import ArtinMatthews.SourceSLocalSheetBorel


set_option backward.privateInPublic true
@[expose] public section

/-! Compatibility of the actual whole product Borel structure with
the product of the local measurable structures. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory Topology
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]

include v in
theorem sourceSWholeUnits_product_borel
    [∀ w : InfinitePlace K, BorelSpace w.Completionˣ]
    [∀ p : S, BorelSpace (p.val.adicCompletion K)ˣ] :
    BorelSpace (SWholeUnits K S) := by
  let : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  let : PolishSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_polish S v
  let e := sourceSWholeSheetSplitMeasurableEquiv S v
  have he : IsInducing e := (sourceSWholeSheetSplit S v).toHomeomorph.isInducing
  exact e.measurableEmbedding.borelSpace he

theorem sourceSheetOtherMeasure_isHaar
    (μarch : ∀ w : InfinitePlace K, Measure w.Completionˣ)
    (μf : ∀ p : S, Measure (p.val.adicCompletion K)ˣ)
    [∀ w : InfinitePlace K, MeasurableMul w.Completionˣ] [∀ p : S, MeasurableMul (p.val.adicCompletion K)ˣ]
    [∀ w, SigmaFinite (μarch w)] [∀ p, SigmaFinite (μf p)]
    [∀ w, (μarch w).IsHaarMeasure] [∀ p, (μf p).IsHaarMeasure] :
    (sourceSheetOtherMeasure S v μarch μf).IsHaarMeasure := by
  let μo := fun w : {w : InfinitePlace K // w ≠ v} => μarch w.val
  have : (Measure.pi μo).IsHaarMeasure := Measure.pi.isHaarMeasure _
  have : (Measure.pi μf).IsHaarMeasure := Measure.pi.isHaarMeasure _
  change ((Measure.pi μo).prod (Measure.pi μf)).IsHaarMeasure
  infer_instance

end
end ArtinMatthews.SourcePhysical
