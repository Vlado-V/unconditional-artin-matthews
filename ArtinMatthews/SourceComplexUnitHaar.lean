module

public import ArtinMatthews.SourceRealLogHaar
public import ArtinMatthews.SourceComplexUnitPolarHomeomorph
public import ArtinMatthews.SourceComplexPolarCircle


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped ENNReal
noncomputable section

scoped instance sourceComplexUnitsBorelSpace : BorelSpace ℂˣ := by
  constructor
  change (borel ℂ).comap (Units.val : ℂˣ → ℂ) = borel ℂˣ
  rw [← borel_comap]
  congr 1
  exact Units.isEmbedding_val₀.isInducing.eq_induced.symm

/-- The actual complex multiplicative Haar with the manuscript's trace normalization. -/
def sourceComplexUnitHaar : Measure ℂˣ :=
  Measure.map sourceComplexUnitPolarMulEquiv (sourceCircleHaar.prod sourceRealLogHaar)

theorem sourceComplexUnitHaar_isHaar : sourceComplexUnitHaar.IsHaarMeasure := by
  have : sourceCircleHaar.IsHaarMeasure := sourceCircleHaar_isHaar
  exact sourceComplexUnitPolarMulEquiv.isHaarMeasure_map
    (sourceCircleHaar.prod sourceRealLogHaar)
    sourceComplexUnitPolarHomeomorph.continuous sourceComplexUnitPolarHomeomorph.symm.continuous

/-- The unit Haar pushes forward to the actual self-dual additive measure divided
by the squared norm. The origin has zero mass in this equality. -/
theorem sourceComplexUnitHaar_map_val :
    Measure.map (Units.val : ℂˣ → ℂ) sourceComplexUnitHaar =
      sourceComplexTraceMeasure.withDensity (fun z : ℂ => ENNReal.ofReal ((‖z‖ ^ 2)⁻¹)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (sourceComplexUnitPolarMulEquiv : Circle × Multiplicative ℝ → ℂˣ) :=
    sourceComplexUnitPolarHomeomorph.continuous.measurable
  let fU : ℂˣ → ℝ≥0∞ := fun z => f (z : ℂ)
  have hfU : Measurable fU := hf.comp Units.continuous_val.measurable
  rw [lintegral_map hf Units.continuous_val.measurable, sourceComplexUnitHaar]
  change (∫⁻ z, fU z ∂Measure.map sourceComplexUnitPolarMulEquiv
    (sourceCircleHaar.prod sourceRealLogHaar)) = _
  rw [lintegral_map hfU hm]
  have hw : Measurable (fun z : ℂ => ENNReal.ofReal ((‖z‖ ^ 2)⁻¹)) := by fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul sourceComplexTraceMeasure hw hf]
  simp only [Pi.mul_apply]
  rw [sourceComplexTraceMultiplicative_lintegral_circle f hf]
  have : sourceCircleHaar.IsHaarMeasure := sourceCircleHaar_isHaar
  let g : Circle × Multiplicative ℝ → ℝ≥0∞ := fun p => fU (sourceComplexUnitPolarMulEquiv p)
  exact lintegral_prod_symm g (hfU.comp hm).aemeasurable

end
end ArtinMatthews.SourcePhysical
