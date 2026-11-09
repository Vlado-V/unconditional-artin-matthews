module

public import Mathlib.MeasureTheory.Measure.Prod


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

def sourceProductSwapMiddle : (A × B) × C ≃ᵐ (A × C) × B :=
  MeasurableEquiv.prodAssoc.trans
    (((MeasurableEquiv.refl A).prodCongr MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm)

theorem sourceProductSwapMiddle_apply (p : (A × B) × C) :
    sourceProductSwapMiddle p = ((p.1.1,p.2),p.1.2) := rfl

theorem sourceProductSwapMiddle_measurePreserving (μa : Measure A) (μb : Measure B) (μc : Measure C)
    [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (sourceProductSwapMiddle : (A × B) × C → (A × C) × B)
      ((μa.prod μb).prod μc) ((μa.prod μc).prod μb) := by
  have h₁ := measurePreserving_prodAssoc μa μb μc
  have h₂ := (MeasurePreserving.id μa).prod (Measure.measurePreserving_swap (μ := μb) (ν := μc))
  have h₃ := (measurePreserving_prodAssoc μa μc μb).symm MeasurableEquiv.prodAssoc
  exact h₃.comp (h₂.comp h₁)

variable {D Z : Type*} [MeasurableSpace D] [MeasurableSpace Z]

/-- Reorder two retained factors before applying literal local and global insertion maps. -/
theorem sourceProductAssembly_measurePreserving
    (μa : Measure A) (μb : Measure B) (μc : Measure C)
    (μd : Measure D) (μz : Measure Z) [SFinite μa] [SFinite μb] [SFinite μc]
    (f : A × C → D) (g : D × B → Z)
    (hf : MeasurePreserving f (μa.prod μc) μd)
    (hg : MeasurePreserving g (μd.prod μb) μz) :
    MeasurePreserving (fun p : (A × B) × C => g (f (p.1.1,p.2),p.1.2))
      ((μa.prod μb).prod μc) μz := by
  have h₁ := sourceProductSwapMiddle_measurePreserving μa μb μc
  have h₂ := hf.prod (MeasurePreserving.id μb)
  exact hg.comp (h₂.comp h₁)

end
end ArtinMatthews.SourcePhysical
