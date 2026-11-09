module

public import ArtinMatthews.SourceArchProjectiveHyperbolicMeasure
public import ArtinMatthews.SourceArchSpatialLebesgue


set_option backward.privateInPublic true
@[expose] public section

/-! Hyperbolic volume is exactly y^-3 times Cartesian complex-height Lebesgue measure. -/
namespace ArtinMatthews.SourceArchJacquet
open MeasureTheory OAI.CubicEisenstein Set
open scoped ENNReal
noncomputable section

def sourceArchUpperEmbedding (p : SourceArchUpperHalfSpace) : ℂ × ℝ := (p.1, p.2.val)

lemma sourceArchUpperEmbedding_measurableEmbedding : MeasurableEmbedding sourceArchUpperEmbedding :=
  (MeasurableEmbedding.subtype_coe
    (show MeasurableSet {p : ℂ × ℝ | 0 < p.2} from
      (isOpen_lt continuous_const continuous_snd).measurableSet)).comp
        sourceArchUpperCoordinatesHomeomorph.toMeasurableEquiv.measurableEmbedding

lemma sourceArchUpperEmbedding_range :
    range sourceArchUpperEmbedding = {p : ℂ × ℝ | 0 < p.2} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.2.property
  · intro hp
    exact ⟨(p.1, ⟨p.2, hp⟩), rfl⟩

lemma sourceArchUpperEmbedding_euclidean (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceArchUpperEmbedding (sourceArchHyperbolicHomeomorph.symm (euclideanToHyperbolic p)) =
      sourceArchSpatialCoordinates p := by
  let q : SourceArchUpperHalfSpace := ((p 0 : ℂ) + Complex.I * (p 1 : ℂ), ⟨p 2, hp⟩)
  have he : euclideanToHyperbolic p = sourceArchHyperbolicHomeomorph q := by
    rw [euclideanToHyperbolic_positive p hp]
    rfl
  rw [he, Homeomorph.symm_apply_apply, sourceArchSpatialCoordinates_apply]
  apply Prod.ext
  · apply Complex.ext <;> simp [sourceArchUpperEmbedding, q]
  · rfl

lemma sourceArchHyperbolicMeasure_embedding :
    Measure.map sourceArchUpperEmbedding sourceArchHyperbolicMeasure =
      ((volume : Measure (ℂ × ℝ)).restrict {p | 0 < p.2}).withDensity sourceArchAmbientDensity := by
  rw [sourceArchHyperbolicMeasure, hyperbolicVolume,
    Measure.map_map sourceArchUpperEmbedding_measurableEmbedding.measurable
      sourceArchHyperbolicHomeomorph.symm.measurable,
    Measure.map_map
      (sourceArchUpperEmbedding_measurableEmbedding.measurable.comp sourceArchHyperbolicHomeomorph.symm.measurable)
      euclideanToHyperbolic_measurable]
  calc
    _ = Measure.map sourceArchSpatialCoordinates hyperbolicEuclideanVolume := by
      apply Measure.map_congr
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      exact sourceArchUpperEmbedding_euclidean p hp
    _ = _ := sourceArchSpatialCoordinates_hyperbolicVolume

lemma sourceArchHyperbolicMeasure_density :
    sourceArchHyperbolicMeasure =
      ((volume : Measure (ℂ × ℝ)).withDensity sourceArchAmbientDensity).comap sourceArchUpperEmbedding := by
  apply sourceArchUpperEmbedding_measurableEmbedding.map_injective
  rw [sourceArchHyperbolicMeasure_embedding,
    sourceArchUpperEmbedding_measurableEmbedding.map_comap, sourceArchUpperEmbedding_range,
    restrict_withDensity (isOpen_lt continuous_const continuous_snd).measurableSet]

lemma sourceArchHyperbolicMeasure_density_product :
    sourceArchHyperbolicMeasure =
      (((volume : Measure ℂ).prod (volume : Measure ℝ)).withDensity sourceArchAmbientDensity).comap
        sourceArchUpperEmbedding := by
  simpa only [Measure.volume_eq_prod] using sourceArchHyperbolicMeasure_density

lemma sourceArchHyperbolicMeasure_apply (s : Set SourceArchUpperHalfSpace) (hs : MeasurableSet s) :
    sourceArchHyperbolicMeasure s =
      ∫⁻ p in sourceArchUpperEmbedding '' s, ENNReal.ofReal (p.2 ^ 3)⁻¹
        ∂(volume : Measure (ℂ × ℝ)) := by
  rw [sourceArchHyperbolicMeasure_density,
    sourceArchUpperEmbedding_measurableEmbedding.comap_apply,
    withDensity_apply _ (sourceArchUpperEmbedding_measurableEmbedding.measurableSet_image' hs)]
  rfl

instance sourceArchHyperbolicMeasure_sigmaFinite : SigmaFinite sourceArchHyperbolicMeasure := by
  have : SigmaFinite hyperbolicEuclideanVolume := by
    unfold hyperbolicEuclideanVolume hyperbolicDensity
    infer_instance
  have : SigmaFinite (Measure.map sourceArchSpatialCoordinates hyperbolicEuclideanVolume) :=
    sourceArchSpatialCoordinates.measurableEmbedding.sigmaFinite_map
  have : SigmaFinite (Measure.map sourceArchUpperEmbedding sourceArchHyperbolicMeasure) := by
    rw [sourceArchHyperbolicMeasure_embedding, ← sourceArchSpatialCoordinates_hyperbolicVolume]
    infer_instance
  exact SigmaFinite.of_map sourceArchHyperbolicMeasure sourceArchUpperEmbedding_measurableEmbedding.measurable.aemeasurable inferInstance

end
end ArtinMatthews.SourceArchJacquet
