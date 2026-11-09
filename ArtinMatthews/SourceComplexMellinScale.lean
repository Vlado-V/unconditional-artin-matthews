module

public import ArtinMatthews.SourceComplexMellinWeight


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory
noncomputable section

theorem sourceComplexMellinWeight_exp_smul (s z : ℂ) (t : ℝ) (hz : z ≠ 0) :
    sourceComplexMellinWeight s (Real.exp t • z) =
      Complex.exp ((2 * s - 2) * (t : ℂ)) * sourceComplexMellinWeight s z := by
  unfold sourceComplexMellinWeight
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr hz), Real.log_exp,
    Complex.ofReal_add, mul_add, Complex.exp_add]

theorem sourceComplexTraceIntegral_exp_smul (g : ℂ → ℂ) (t : ℝ) :
    (∫ z : ℂ, g (Real.exp t • z) ∂sourceComplexTraceMeasure) =
      (Real.exp (-2 * t) : ℂ) * (∫ z : ℂ, g z ∂sourceComplexTraceMeasure) := by
  have h : |(Real.exp t ^ Module.finrank ℝ ℂ)⁻¹| = Real.exp (-2 * t) := by
    rw [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.mpr (by positivity)),
      ← Real.exp_nat_mul, ← Real.exp_neg]
    norm_num
  simp only [sourceComplexTraceMeasure, integral_smul_measure]
  rw [Measure.integral_comp_smul volume g (Real.exp t), h]
  simp only [RCLike.real_smul_eq_coe_mul]
  exact mul_left_comm _ _ _

/-- The source Mellin integral has the exact logarithmic dilation law. -/
theorem sourceComplexMellin_exp_smul (f : ℂ → ℂ) (s : ℂ) (t : ℝ) :
    sourceComplexMellin (fun z => f (Real.exp t • z)) s =
      Complex.exp (-(2 * s) * (t : ℂ)) * sourceComplexMellin f s := by
  let k := (2 * s - 2) * (t : ℂ)
  let g : ℂ → ℂ := fun z => f z * sourceComplexMellinWeight s z
  have hInt : (∫ z : ℂ, f (Real.exp t • z) * sourceComplexMellinWeight s z
      ∂sourceComplexTraceMeasure) =
      ∫ z : ℂ, Complex.exp (-k) * g (Real.exp t • z) ∂sourceComplexTraceMeasure := by
    apply integral_congr_ae
    filter_upwards [sourceComplexTraceMeasure_ae_ne_zero] with z hz
    change _ = Complex.exp (-k) * (f (Real.exp t • z) * sourceComplexMellinWeight s (Real.exp t • z))
    rw [sourceComplexMellinWeight_exp_smul s z t hz]
    change _ = Complex.exp (-k) * (f (Real.exp t • z) * (Complex.exp k * sourceComplexMellinWeight s z))
    calc
      _ = (Complex.exp (-k) * Complex.exp k) *
          (f (Real.exp t • z) * sourceComplexMellinWeight s z) := by
        rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
      _ = _ := by ring
  unfold sourceComplexMellin
  rw [hInt, integral_const_mul, sourceComplexTraceIntegral_exp_smul,
    Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  dsimp [k]
  push_cast
  ring

end
end ArtinMatthews.VaryingKummerAnalytic
