module

public import ArtinMatthews.SourceArchHyperbolicDensity
public import Mathlib.MeasureTheory.Measure.OpenPos


set_option backward.privateInPublic true
@[expose] public section

/-! The actual hyperbolic density is positive and continuous on the open upper chart. -/
namespace ArtinMatthews.SourceArchJacquet
open MeasureTheory MeasureTheory.Measure Topology Set
open scoped ENNReal
noncomputable section

lemma sourceArchUpperEmbedding_isOpenEmbedding : IsOpenEmbedding sourceArchUpperEmbedding :=
  (isOpen_lt continuous_const continuous_snd).isOpenEmbedding_subtypeVal.comp
    sourceArchUpperCoordinatesHomeomorph.isOpenEmbedding

instance sourceArchUpperHalfSpace_locallyCompact : LocallyCompactSpace SourceArchUpperHalfSpace :=
  sourceArchUpperEmbedding_isOpenEmbedding.locallyCompactSpace

def sourceArchUpperLebesgue : Measure SourceArchUpperHalfSpace :=
  (volume : Measure (ℂ × ℝ)).comap sourceArchUpperEmbedding

instance sourceArchUpperLebesgue_finiteOnCompacts : IsFiniteMeasureOnCompacts sourceArchUpperLebesgue :=
  IsFiniteMeasureOnCompacts.comap' volume sourceArchUpperEmbedding_isOpenEmbedding.continuous
    sourceArchUpperEmbedding_measurableEmbedding

instance sourceArchUpperLebesgue_openPos : IsOpenPosMeasure sourceArchUpperLebesgue :=
  IsOpenPosMeasure.comap volume sourceArchUpperEmbedding_isOpenEmbedding

def sourceArchUpperDensity (p : SourceArchUpperHalfSpace) : ℝ := (p.2.val ^ 3)⁻¹

lemma sourceArchUpperDensity_pos (p : SourceArchUpperHalfSpace) : 0 < sourceArchUpperDensity p :=
  inv_pos.mpr (pow_pos p.2.property 3)

lemma sourceArchUpperDensity_continuous : Continuous sourceArchUpperDensity :=
  ((continuous_subtype_val.comp continuous_snd).pow 3).inv₀
    (fun p => pow_ne_zero 3 p.2.property.ne')

lemma sourceArchHyperbolicMeasure_upperDensity :
    sourceArchHyperbolicMeasure =
      sourceArchUpperLebesgue.withDensity (fun p => ENNReal.ofReal (sourceArchUpperDensity p)) := by
  have hf : MeasurePreserving sourceArchUpperEmbedding sourceArchUpperLebesgue
      ((volume : Measure (ℂ × ℝ)).restrict {p | 0 < p.2}) := by
    refine ⟨sourceArchUpperEmbedding_measurableEmbedding.measurable, ?_⟩
    rw [sourceArchUpperLebesgue, sourceArchUpperEmbedding_measurableEmbedding.map_comap,
      sourceArchUpperEmbedding_range]
  have hd : sourceArchAmbientDensity ∘ sourceArchUpperEmbedding =
      (fun p => ENNReal.ofReal (sourceArchUpperDensity p)) := by
    rfl
  apply sourceArchUpperEmbedding_measurableEmbedding.map_injective
  rw [sourceArchHyperbolicMeasure_embedding, ← hd]
  exact (sourceArchMeasurePreserving_density hf sourceArchAmbientDensity
    sourceArchAmbientDensity_measurable).map_eq.symm

instance sourceArchHyperbolicMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts sourceArchHyperbolicMeasure := by
  rw [sourceArchHyperbolicMeasure_upperDensity]
  let : IsLocallyFiniteMeasure
      (sourceArchUpperLebesgue.withDensity (fun p => ENNReal.ofReal (sourceArchUpperDensity p))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal sourceArchUpperDensity_continuous
  infer_instance

instance sourceArchHyperbolicMeasure_openPos : IsOpenPosMeasure sourceArchHyperbolicMeasure := by
  rw [sourceArchHyperbolicMeasure_upperDensity]
  apply Measure.AbsolutelyContinuous.isOpenPosMeasure (μ := sourceArchUpperLebesgue)
  exact withDensity_absolutelyContinuous' sourceArchUpperDensity_continuous.measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun p => (ENNReal.ofReal_pos.mpr (sourceArchUpperDensity_pos p)).ne')

lemma sourceArchHyperbolicMeasure_sFinite : SFinite sourceArchHyperbolicMeasure := inferInstance

instance sourceArchHyperbolicMeasure_smulInvariant :
    SMulInvariantMeasure (Matrix.ProjGenLinGroup (Fin 2) ℂ) SourceArchUpperHalfSpace sourceArchHyperbolicMeasure where
  measure_preimage_smul a _s hs :=
    (sourceArchHyperbolicMeasure_preserving a).measure_preimage hs.nullMeasurableSet

end
end ArtinMatthews.SourceArchJacquet
