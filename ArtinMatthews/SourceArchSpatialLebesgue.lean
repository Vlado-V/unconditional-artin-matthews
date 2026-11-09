module

public import ArtinMatthews.SourceArchHyperbolicCoordinates
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity


set_option backward.privateInPublic true
@[expose] public section

/-! Literal Cartesian and complex-height coordinates preserve Lebesgue volume. -/
namespace ArtinMatthews.SourceArchJacquet
open MeasureTheory OAI.CubicEisenstein
open scoped ENNReal
noncomputable section

def sourceArchSpatialCoordinates : EuclideanSpatial ≃ᵐ (ℂ × ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
      (((MeasurableEquiv.refl ℝ).prodCongr
        (MeasurableEquiv.finTwoArrow.trans Complex.measurableEquivRealProd.symm)).trans
          (MeasurableEquiv.prodComm : (ℝ × ℂ) ≃ᵐ (ℂ × ℝ))))

lemma sourceArchSpatialCoordinates_apply (p : EuclideanSpatial) :
    sourceArchSpatialCoordinates p = ((⟨p 0, p 1⟩ : ℂ), p 2) := rfl

lemma sourceArchSpatialCoordinates_volume :
    MeasurePreserving sourceArchSpatialCoordinates volume volume := by
  have h0 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have h2 : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr
        (MeasurableEquiv.finTwoArrow.trans Complex.measurableEquivRealProd.symm)) volume volume :=
    (MeasurePreserving.id volume).prod
      (Complex.volume_preserving_equiv_real_prod.symm.comp (volume_preserving_finTwoArrow ℝ))
  have h3 : MeasurePreserving (MeasurableEquiv.prodComm : (ℝ × ℂ) ≃ᵐ (ℂ × ℝ)) volume volume :=
    Measure.measurePreserving_swap
  exact h3.comp (h2.comp (h1.comp h0))

lemma sourceArchMeasurePreserving_density {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    (w : B → ℝ≥0∞) (hw : Measurable w) :
    MeasurePreserving f (μ.withDensity (w ∘ f)) (ν.withDensity w) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  exact hf.setLIntegral_comp_preimage hs hw

def sourceArchAmbientDensity (p : ℂ × ℝ) : ℝ≥0∞ := ENNReal.ofReal (p.2 ^ 3)⁻¹

lemma sourceArchAmbientDensity_measurable : Measurable sourceArchAmbientDensity := by
  unfold sourceArchAmbientDensity
  fun_prop

lemma sourceArchSpatialCoordinates_positive :
    sourceArchSpatialCoordinates ⁻¹' {p : ℂ × ℝ | 0 < p.2} = euclideanUpperHalf := by
  ext p
  rfl

lemma sourceArchSpatialCoordinates_hyperbolicVolume :
    Measure.map sourceArchSpatialCoordinates hyperbolicEuclideanVolume =
      ((volume : Measure (ℂ × ℝ)).restrict {p | 0 < p.2}).withDensity sourceArchAmbientDensity := by
  have hm := sourceArchSpatialCoordinates_volume.restrict_preimage
    (show MeasurableSet {p : ℂ × ℝ | 0 < p.2} from isOpen_lt continuous_const continuous_snd |>.measurableSet)
  rw [sourceArchSpatialCoordinates_positive] at hm
  have hd : sourceArchAmbientDensity ∘ sourceArchSpatialCoordinates = hyperbolicDensity := rfl
  simpa only [hd, hyperbolicEuclideanVolume] using
    (sourceArchMeasurePreserving_density hm sourceArchAmbientDensity sourceArchAmbientDensity_measurable).map_eq

end
end ArtinMatthews.SourceArchJacquet
