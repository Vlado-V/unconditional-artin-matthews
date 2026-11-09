module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set
noncomputable section

/-- Translation of logarithmic radius by a measurable function of the other
coordinates preserves the product measure. -/
theorem sourceLogRadial_shear_measurePreserving {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (h : A → ℝ) (hh : Measurable h) :
    MeasurePreserving (fun p : A × ℝ => (p.1, p.2 + h p.1))
      (μ.prod volume) (μ.prod volume) := by
  have hm : Measurable (fun p : A × ℝ => (p.1, p.2 + h p.1)) :=
    measurable_fst.prodMk (measurable_snd.add (hh.comp measurable_fst))
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs), Measure.prod_apply hs]
  apply lintegral_congr
  intro a
  have ht := measurePreserving_add_right (volume : Measure ℝ) (h a)
  have hpre : MeasurableSet (Prod.mk a ⁻¹' s) := measurable_prodMk_left hs
  change volume ((fun u : ℝ => u + h a) ⁻¹' (Prod.mk a ⁻¹' s)) = volume (Prod.mk a ⁻¹' s)
  rw [← Measure.map_apply ht.measurable hpre, ht.map_eq]

end
end ArtinMatthews.SourcePhysical
