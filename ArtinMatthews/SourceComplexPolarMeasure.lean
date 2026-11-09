module

public import ArtinMatthews.SourceLogRadialMeasure
public import ArtinMatthews.SourceComplexTraceFourier
public import Mathlib.Analysis.SpecialFunctions.PolarCoord


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set
open ArtinMatthews.VaryingKummerAnalytic
open scoped ENNReal Real
noncomputable section

def sourceComplexPolar (r θ : ℝ) : ℂ := r * (Real.cos θ + Real.sin θ * Complex.I)

theorem sourceComplexPolar_eq (r θ : ℝ) :
    sourceComplexPolar r θ = Complex.polarCoord.symm (r,θ) := by
  rw [Complex.polarCoord_symm_apply, sourceComplexPolar]

theorem sourceComplexPolar_continuous : Continuous (fun p : ℝ × ℝ => sourceComplexPolar p.1 p.2) := by
  unfold sourceComplexPolar
  fun_prop

theorem sourceComplexPolar_norm (r θ : ℝ) : ‖sourceComplexPolar r θ‖ = |r| := by
  rw [sourceComplexPolar_eq]
  exact Complex.norm_polarCoord_symm (r,θ)

/-- The literal multiplicative trace measure has Lebesgue density in log squared norm
and unnormalized angle, with no undetermined scalar. -/
theorem sourceComplexTraceMultiplicative_lintegral (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : ℂ, ENNReal.ofReal ((‖z‖ ^ 2)⁻¹) * f z ∂sourceComplexTraceMeasure) =
      ∫⁻ t : ℝ, ∫⁻ θ in Ioo (-π) π, f (sourceComplexPolar (Real.exp (t / 2)) θ) := by
  let g : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal p.1 * (ENNReal.ofReal ((‖sourceComplexPolar p.1 p.2‖ ^ 2)⁻¹) *
      f (sourceComplexPolar p.1 p.2))
  have hg : Measurable g := by
    apply (measurable_fst.ennreal_ofReal).mul
    apply Measurable.mul
    · exact (((sourceComplexPolar_continuous.norm.pow 2).measurable).inv).ennreal_ofReal
    · exact hf.comp sourceComplexPolar_continuous.measurable
  have hp : (∫⁻ z : ℂ, ENNReal.ofReal ((‖z‖ ^ 2)⁻¹) * f z) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, g p := by
    rw [← Complex.lintegral_comp_polarCoord_symm, _root_.polarCoord_target]
    congr 1
    funext p
    rw [← sourceComplexPolar_eq p.1 p.2]
    rfl
  rw [sourceComplexTraceMeasure, lintegral_smul_measure, hp]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    ← Measure.prod_restrict, lintegral_prod g hg.aemeasurable]
  change (2 : ℝ≥0∞) * (∫⁻ r in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π, g (r, θ)) = _
  rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2 / r) *
          (∫⁻ θ in Ioo (-π) π, f (sourceComplexPolar r θ)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr' : 0 < r := hr
      have hcoeff : (2 : ℝ≥0∞) *
          (ENNReal.ofReal r * ENNReal.ofReal ((r ^ 2)⁻¹)) = ENNReal.ofReal (2 / r) := by
        rw [← ENNReal.ofReal_mul hr'.le]
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        field_simp
      simp only [g, sourceComplexPolar_norm, abs_of_pos hr', ← mul_assoc]
      rw [lintegral_const_mul' _ _ (by simp [ENNReal.mul_ne_top]), ← mul_assoc, hcoeff]
    _ = _ := sourceLogRadial_lintegral (fun r => ∫⁻ θ in Ioo (-π) π, f (sourceComplexPolar r θ))

end
end ArtinMatthews.SourcePhysical
