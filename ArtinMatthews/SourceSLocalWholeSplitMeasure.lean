module

public import ArtinMatthews.SourceSLocalWholeSplit
public import Mathlib.MeasureTheory.Constructions.Pi


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite products of local measures split off the chosen
infinite unit without changing any factor normalization. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]

omit [NumberField K] in
@[instance_reducible]
private def sourceSheetChosenUnique : Unique {w : InfinitePlace K // w = v} where
  default := ⟨v,rfl⟩
  uniq w := Subtype.ext w.property

private def sourceSWholeArchSplitMeasurableEquiv :
    (∀ w : InfinitePlace K, w.Completionˣ) ≃ᵐ
      v.Completionˣ × (∀ w : {w : InfinitePlace K // w ≠ v}, w.val.Completionˣ) := by
  let : Unique {w : InfinitePlace K // w = v} := sourceSheetChosenUnique v
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun w : InfinitePlace K => w.Completionˣ)
      (fun w => w = v)).trans
    ((MeasurableEquiv.piUnique (fun w : {w : InfinitePlace K // w = v} => w.val.Completionˣ)).prodCongr
      (MeasurableEquiv.refl _))

def sourceSWholeSheetSplitMeasurableEquiv :
    SWholeUnits K S ≃ᵐ v.Completionˣ × SNormOneOtherUnits S v :=
  ((sourceSWholeArchSplitMeasurableEquiv v).prodCongr (MeasurableEquiv.refl _)).trans
    MeasurableEquiv.prodAssoc

@[simp] theorem sourceSWholeSheetSplitMeasurableEquiv_apply (x : SWholeUnits K S) :
    sourceSWholeSheetSplitMeasurableEquiv S v x = sourceSWholeSheetSplit S v x := rfl

@[simp] theorem sourceSWholeSheetSplitMeasurableEquiv_symm_apply
    (y : v.Completionˣ × SNormOneOtherUnits S v) :
    (sourceSWholeSheetSplitMeasurableEquiv S v).symm y = (sourceSWholeSheetSplit S v).symm y := by
  apply (sourceSWholeSheetSplitMeasurableEquiv S v).injective
  rw [MeasurableEquiv.apply_symm_apply, sourceSWholeSheetSplitMeasurableEquiv_apply]
  exact ((sourceSWholeSheetSplit S v).apply_symm_apply y).symm

variable (μarch : ∀ w : InfinitePlace K, Measure w.Completionˣ)
variable (μf : ∀ p : S, Measure (p.val.adicCompletion K)ˣ)

/-- The unchanged product of all local measures away from the chosen place. -/
def sourceSheetOtherMeasure : Measure (SNormOneOtherUnits S v) :=
  (Measure.pi (fun w : {w : InfinitePlace K // w ≠ v} => μarch w.val)).prod (Measure.pi μf)

variable [∀ w, SigmaFinite (μarch w)] [∀ p, SigmaFinite (μf p)]

theorem sourceSWholeSheetSplit_measurePreserving :
    MeasurePreserving (sourceSWholeSheetSplit S v)
      ((Measure.pi μarch).prod (Measure.pi μf))
      ((μarch v).prod (sourceSheetOtherMeasure S v μarch μf)) := by
  let : Unique {w : InfinitePlace K // w = v} := sourceSheetChosenUnique v
  let μo := Measure.pi (fun w : {w : InfinitePlace K // w ≠ v} => μarch w.val)
  have hπ := measurePreserving_piEquivPiSubtypeProd μarch (fun w => w = v)
  let : Fintype {w : InfinitePlace K // w = v} :=
    Subtype.fintype (fun w : InfinitePlace K => w = v)
  have hv := measurePreserving_piUnique (fun w : {w : InfinitePlace K // w = v} => μarch w.val)
  have hArch : MeasurePreserving (sourceSWholeArchSplitMeasurableEquiv v)
      (Measure.pi μarch) ((μarch v).prod μo) :=
    (hv.prod (MeasurePreserving.id μo)).comp hπ
  have h := (measurePreserving_prodAssoc (μarch v) μo (Measure.pi μf)).comp
    (hArch.prod (MeasurePreserving.id (Measure.pi μf)))
  exact h

theorem sourceSWholeSheetSplit_map :
    Measure.map (sourceSWholeSheetSplit S v) ((Measure.pi μarch).prod (Measure.pi μf)) =
      (μarch v).prod (sourceSheetOtherMeasure S v μarch μf) :=
  (sourceSWholeSheetSplit_measurePreserving S v μarch μf).map_eq

theorem sourceSWholeSheetSplit_symm_measurePreserving :
    MeasurePreserving (sourceSWholeSheetSplit S v).symm
      ((μarch v).prod (sourceSheetOtherMeasure S v μarch μf))
      ((Measure.pi μarch).prod (Measure.pi μf)) := by
  have h : MeasurePreserving (sourceSWholeSheetSplitMeasurableEquiv S v)
      ((Measure.pi μarch).prod (Measure.pi μf)) ((μarch v).prod (sourceSheetOtherMeasure S v μarch μf)) :=
    sourceSWholeSheetSplit_measurePreserving S v μarch μf
  have h' := MeasurePreserving.symm (sourceSWholeSheetSplitMeasurableEquiv S v) h
  have hfun : ((sourceSWholeSheetSplitMeasurableEquiv S v).symm :
      v.Completionˣ × SNormOneOtherUnits S v → SWholeUnits K S) =
      ((sourceSWholeSheetSplit S v).symm : v.Completionˣ × SNormOneOtherUnits S v → SWholeUnits K S) :=
    funext (sourceSWholeSheetSplitMeasurableEquiv_symm_apply S v)
  exact hfun ▸ h'

end
end ArtinMatthews.SourcePhysical
