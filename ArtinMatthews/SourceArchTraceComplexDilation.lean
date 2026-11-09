module

public import ArtinMatthews.SourceComplexTraceFourier
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.RingTheory.Complex


set_option backward.privateInPublic true
@[expose] public section

/-! Multiplication by a nonzero complex scalar on the literal self-dual
trace measure has the real two-dimensional determinant `‖b‖²`. -/

namespace ArtinMatthews.SourceArchJacquet
open ArtinMatthews.VaryingKummerAnalytic MeasureTheory
open scoped ENNReal
noncomputable section

/-- The inverse Jacobian of complex multiplication for the actual trace measure. -/
theorem sourceArchTraceMeasure_map_mul_left (b : ℂ) (hb : b ≠ 0) :
    Measure.map (fun x : ℂ => b * x) sourceComplexTraceMeasure =
      ENNReal.ofReal ((‖b‖ ^ 2)⁻¹) • sourceComplexTraceMeasure := by
  have : sourceComplexTraceMeasure.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul volume (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hdet : LinearMap.det (Algebra.lmul ℝ ℂ b) = ‖b‖ ^ 2 := by
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hd : LinearMap.det (Algebra.lmul ℝ ℂ b) ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hb)
  change Measure.map (Algebra.lmul ℝ ℂ b) sourceComplexTraceMeasure = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hd, hdet,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ‖b‖))]

/-- Change variables `z = b*x` in an integral against the actual trace measure. -/
theorem sourceArchTraceIntegral_mul_left (f : ℂ → ℂ) (b : ℂ) (hb : b ≠ 0) :
    (∫ x : ℂ, f (b * x) ∂sourceComplexTraceMeasure) =
      (((‖b‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∫ z : ℂ, f z ∂sourceComplexTraceMeasure := by
  calc
    _ = ∫ z, f z ∂Measure.map (fun x : ℂ => b * x) sourceComplexTraceMeasure :=
      ((measurableEmbedding_mulLeft₀ hb).integral_map f).symm
    _ = _ := by
      rw [sourceArchTraceMeasure_map_mul_left b hb, integral_smul_measure,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg ‖b‖)), Complex.real_smul]

end
end ArtinMatthews.SourceArchJacquet
