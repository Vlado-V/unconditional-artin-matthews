module

public import ArtinMatthews.SourceComplexMellinSchwartz
public import ArtinMatthews.SourceComplexAdelicCharacter
public import Mathlib.Analysis.Complex.Isometry


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory NumberField NumberField.InfinitePlace
open scoped SchwartzMap BigOperators NumberField Classical
noncomputable section

/-- Pull back a complex Schwartz factor by division by a nonzero complex scalar. -/
def sourceComplexSchwartzDivDilate (t : ℂˣ) (f : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) t⁻¹) f

theorem sourceComplexSchwartzDivDilate_apply (t : ℂˣ) (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    sourceComplexSchwartzDivDilate t f z = f (z / (t : ℂ)) := by
  change f ((t⁻¹ : ℂˣ) • z) = _
  rw [Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm]

/-- The complex trace measure has the literal norm-squared division Jacobian. -/
theorem sourceComplexTraceIntegral_div (t : ℂˣ) (f : ℂ → ℂ) :
    (∫ z, f (z / (t : ℂ)) ∂sourceComplexTraceMeasure) =
      ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ) * ∫ z, f z ∂sourceComplexTraceMeasure := by
  let r := ‖(t : ℂ)‖
  have hr : 0 < r := norm_pos_iff.mpr t.ne_zero
  let a : Circle := ⟨(r : ℂ) / (t : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_self hr.ne'⟩
  have ha (z : ℂ) : rotation a (r⁻¹ • z) = z / (t : ℂ) := by
    rw [rotation_apply, RCLike.real_smul_eq_coe_mul]
    change (r : ℂ) / (t : ℂ) * ((r⁻¹ : ℝ) * z) = _
    simp only [Complex.ofReal_inv, div_eq_mul_inv]
    calc
      _ = ((r : ℂ) * (r : ℂ)⁻¹) * (z * (t : ℂ)⁻¹) := by ac_rfl
      _ = _ := by rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_mul]
  unfold sourceComplexTraceMeasure
  simp only [integral_smul_measure, ENNReal.toReal_ofNat]
  simp_rw [← ha]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun z => f (rotation a z)) hr.le,
    (rotation a).measurePreserving.integral_comp
      (rotation a).toHomeomorph.measurableEmbedding f,
    Complex.finrank_real_complex]
  simp only [RCLike.real_smul_eq_coe_mul]
  change (2 : ℂ) * (((r ^ 2 : ℝ) : ℂ) * _) = ((r ^ 2 : ℝ) : ℂ) * (2 * _)
  ac_rfl

theorem sourceComplexTraceFourier_divDilate (t : ℂˣ) (f : 𝓢(ℂ, ℂ)) (y : ℂ) :
    sourceComplexTraceFourier (sourceComplexSchwartzDivDilate t f) y =
      ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ) * sourceComplexTraceFourier f ((t : ℂ) * y) := by
  let g (z : ℂ) := Real.fourierChar (-(2 * (z * ((t : ℂ) * y)).re)) • f z
  have hg (z : ℂ) : Real.fourierChar (-(2 * (z * y).re)) •
      sourceComplexSchwartzDivDilate t f z = g (z / (t : ℂ)) := by
    rw [sourceComplexSchwartzDivDilate_apply]
    dsimp only [g]
    rw [← mul_assoc, div_mul_cancel₀ _ t.ne_zero]
  unfold sourceComplexTraceFourier
  simp_rw [hg]
  exact sourceComplexTraceIntegral_div t g

variable (K : Type) [Field K] [NumberField K]
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

/-- Coordinatewise complex division transports the actual archimedean tensor transform. -/
theorem sourceNumberFieldComplexFourier_divDilate
    (t : CPlaces → ℂˣ) (f : CPlaces → 𝓢(ℂ, ℂ)) (y : CPlaces → ℂ) :
    sourceNumberFieldComplexFourier K (fun x => ∏ v, f v (x v / (t v : ℂ))) y =
      ((∏ v, ‖(t v : ℂ)‖ ^ 2 : ℝ) : ℂ) *
        sourceNumberFieldComplexFourier K (fun x => ∏ v, f v (x v))
          (fun v => (t v : ℂ) * y v) := by
  simp_rw [← sourceComplexSchwartzDivDilate_apply]
  rw [sourceNumberFieldComplexFourier_eq, sourceNumberFieldComplexFourier_eq,
    source_complex_product_fourier_tensor (fun v => sourceComplexSchwartzDivDilate (t v) (f v)),
    source_complex_product_fourier_tensor (fun v => f v)]
  simp_rw [sourceComplexTraceFourier_divDilate]
  rw [Finset.prod_mul_distrib, Complex.ofReal_prod]

end
end ArtinMatthews.VaryingKummerAnalytic
