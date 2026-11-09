module

public import ArtinMatthews.SourceArchHyperbolicRegularity
public import ArtinMatthews.SourceArchRadialFlow


set_option backward.privateInPublic true
@[expose] public section

/-! Vertical hyperbolic dilation has its exact modular factor. -/
namespace ArtinMatthews.SourceArchJacquet
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
noncomputable section

def sourceArchRadialAmbient (t : ℝ) : ℂ × ℝ → ℂ × ℝ :=
  Prod.map id (fun y => Real.exp t * y)

lemma sourceArchRadialAmbient_preserving (t : ℝ) :
    MeasurePreserving (sourceArchRadialAmbient t) (volume : Measure (ℂ × ℝ))
      (ENNReal.ofReal ((Real.exp t)⁻¹) • volume) := by
  refine ⟨by unfold sourceArchRadialAmbient; fun_prop, ?_⟩
  rw [Measure.volume_eq_prod]
  change Measure.map (Prod.map id (fun y => Real.exp t * y))
    ((volume : Measure ℂ).prod (volume : Measure ℝ)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
    Real.map_volume_mul_left (Real.exp_pos t).ne', abs_of_pos (inv_pos.mpr (Real.exp_pos t)),
    Measure.prod_smul_right]

lemma sourceArchRadialAmbient_upper_preimage (t : ℝ) :
    sourceArchRadialAmbient t ⁻¹' {p : ℂ × ℝ | 0 < p.2} = {p | 0 < p.2} := by
  ext p
  exact mul_pos_iff_of_pos_left (Real.exp_pos t)

lemma sourceArchRadialAmbient_density (t : ℝ) :
    ((ENNReal.ofReal ((Real.exp t) ^ 3) • sourceArchAmbientDensity) ∘ sourceArchRadialAmbient t) =
      sourceArchAmbientDensity := by
  funext p
  change ENNReal.ofReal ((Real.exp t) ^ 3) *
    ENNReal.ofReal ((Real.exp t * p.2) ^ 3)⁻¹ = ENNReal.ofReal (p.2 ^ 3)⁻¹
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow, mul_inv_rev]
  calc
    (Real.exp t) ^ 3 * ((p.2 ^ 3)⁻¹ * ((Real.exp t) ^ 3)⁻¹) =
        ((Real.exp t) ^ 3 * ((Real.exp t) ^ 3)⁻¹) * (p.2 ^ 3)⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero 3 (Real.exp_pos t).ne'), one_mul]

lemma sourceArchRadialAmbient_hyperbolic (t : ℝ) :
    Measure.map (sourceArchRadialAmbient t)
      (((volume : Measure (ℂ × ℝ)).restrict {p | 0 < p.2}).withDensity sourceArchAmbientDensity) =
      ENNReal.ofReal (Real.exp (2 * t)) •
        (((volume : Measure (ℂ × ℝ)).restrict {p | 0 < p.2}).withDensity sourceArchAmbientDensity) := by
  have hm := (sourceArchRadialAmbient_preserving t).restrict_preimage
    (show MeasurableSet {p : ℂ × ℝ | 0 < p.2} from
      (isOpen_lt continuous_const continuous_snd).measurableSet)
  rw [sourceArchRadialAmbient_upper_preimage, Measure.restrict_smul] at hm
  have hd := sourceArchMeasurePreserving_density hm
    (ENNReal.ofReal ((Real.exp t) ^ 3) • sourceArchAmbientDensity)
    (measurable_const.smul sourceArchAmbientDensity_measurable)
  rw [sourceArchRadialAmbient_density] at hd
  rw [hd.map_eq, withDensity_smul_measure, withDensity_smul _ sourceArchAmbientDensity_measurable,
    smul_smul]
  have he : (Real.exp t)⁻¹ * (Real.exp t) ^ 3 = Real.exp (2 * t) := by
    rw [show (Real.exp t) ^ 3 = Real.exp t * (Real.exp t) ^ 2 by ring,
      ← mul_assoc, inv_mul_cancel₀ (Real.exp_pos t).ne', one_mul]
    rw [show 2 * t = t + t by ring, Real.exp_add]
    ring
  rw [← ENNReal.ofReal_mul (by positivity), he]

lemma sourceArchRadialPoint_measurable (t : ℝ) : Measurable (sourceArchRadialPoint t) := by
  unfold sourceArchRadialPoint
  fun_prop

lemma sourceArchRadialPoint_hyperbolicMeasure (t : ℝ) :
    Measure.map (sourceArchRadialPoint t) sourceArchHyperbolicMeasure =
      ENNReal.ofReal (Real.exp (2 * t)) • sourceArchHyperbolicMeasure := by
  apply sourceArchUpperEmbedding_measurableEmbedding.map_injective
  rw [Measure.map_smul _ sourceArchUpperEmbedding_measurableEmbedding.measurable.aemeasurable,
    sourceArchHyperbolicMeasure_embedding,
    Measure.map_map sourceArchUpperEmbedding_measurableEmbedding.measurable
      (sourceArchRadialPoint_measurable t)]
  have he : sourceArchUpperEmbedding ∘ sourceArchRadialPoint t =
      sourceArchRadialAmbient t ∘ sourceArchUpperEmbedding := rfl
  rw [he, ← Measure.map_map (sourceArchRadialAmbient_preserving t).measurable
    sourceArchUpperEmbedding_measurableEmbedding.measurable,
    sourceArchHyperbolicMeasure_embedding, sourceArchRadialAmbient_hyperbolic]

end
end ArtinMatthews.SourceArchJacquet
