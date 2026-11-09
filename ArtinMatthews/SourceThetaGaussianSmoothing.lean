module

public import ArtinMatthews.SourceThetaGaussianKernel
public import ArtinMatthews.SourceLogMellinCoordinate
public import ArtinMatthews.ReflectionGaussianWeight
public import Mathlib.MeasureTheory.Integral.Prod


set_option backward.privateInPublic true
@[expose] public section

/-! Exact source03 Gaussian smoothing, with the literal positive scaling
in V(uT). Absolute Fubini on the zero line gives the same P_G used in B_m. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Complex SourcePhysical VaryingKummerAnalytic
noncomputable section

/-- Smoothing on the physical multiplicative radial measure dT/T. -/
def sourceThetaGaussianSmoothing (C₀ A₀ : ℝ) (r : ℕ) (V : ℝ → ℂ) (u : ℝ) : ℂ :=
  mellin (fun T : ℝ => sourceThetaGaussianKernel C₀ A₀ r T * V (u * T)) 0

private theorem sourceTheta_smoothing_log_input_integrable (V : ℝ → ℂ) (hV : MellinConvergent V 0)
    {u : ℝ} (hu : 0 < u) : Integrable (fun x : ℝ => V (u * Real.exp x)) := by
  have h := (MellinConvergent.comp_mul_left (f := V) (s := 0) hu).mpr hV
  rw [sourceMellinConvergent_iff_log] at h
  simpa only [zero_mul, Complex.exp_zero, one_mul] using h

/-- The source Gaussian smoothing identity from the genuine input Mellin
symbol. The only input about V is its Mellin integral and convergence. -/
theorem sourceThetaGaussianSmoothing_eq_reflectionGaussian {C₀ A₀ : ℝ}
    (hC₀ : 0 < C₀) (hA₀ : 0 < A₀) (r : ℕ) (V : ℝ → ℂ) (hV₀ : MellinConvergent V 0)
    (hV : ∀ t : ℝ, mellin V ((t : ℂ) * I) = sourceThetaMellinSymbol C₀ A₀ r ((t : ℂ) * I))
    {u : ℝ} (hu : 0 < u) : sourceThetaGaussianSmoothing C₀ A₀ r V u = (reflectionGaussian u : ℂ) := by
  let W (x : ℝ) := V (u * Real.exp x)
  let R (t : ℝ) := sourceThetaReciprocalMellin C₀ A₀ r ((t : ℂ) * I)
  let A (x t : ℝ) := R t * Complex.exp (((t : ℂ) * I) * (x : ℂ)) * W x
  let c : ℝ := 1 / (2 * Real.pi)
  have hW : Integrable W := sourceTheta_smoothing_log_input_integrable V hV₀ hu
  have hR : Integrable R := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add, R] using
      sourceThetaReciprocalMellin_verticalIntegrable C₀ A₀ r 0
  have hphase (t x : ℝ) : ‖Complex.exp (((t : ℂ) * I) * (x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hA : Integrable (Function.uncurry A) ((volume : Measure ℝ).prod volume) := by
    have hexp : Continuous (fun p : ℝ × ℝ => Complex.exp (((p.2 : ℂ) * I) * (p.1 : ℂ))) := by fun_prop
    apply (hW.norm.mul_prod hR.norm).mono'
      (((hR.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))).mul
        hexp.aestronglyMeasurable).mul (hW.aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))))
    filter_upwards [] with p
    change ‖R p.2 * Complex.exp (((p.2 : ℂ) * I) * (p.1 : ℂ)) * W p.1‖ ≤ ‖W p.1‖ * ‖R p.2‖
    rw [norm_mul, norm_mul, hphase, mul_one, mul_comm]
  have hA₁ (x : ℝ) : sourceThetaGaussianLogKernel C₀ A₀ r x * W x = c • ∫ t : ℝ, A x t := by
    unfold sourceThetaGaussianLogKernel sourceThetaGaussianLogKernelLine
    rw [smul_mul_assoc, ← integral_mul_const]
    simp only [Complex.ofReal_zero, zero_add, c, A, R]
  have hInner (t : ℝ) : (∫ x : ℝ, Complex.exp (((t : ℂ) * I) * (x : ℂ)) * W x) =
      (u : ℂ) ^ (-((t : ℂ) * I)) * mellin V ((t : ℂ) * I) := by
    exact (sourceMellin_eq_log (fun T => V (u * T)) ((t : ℂ) * I)).symm.trans
      (by simpa only [smul_eq_mul] using mellin_comp_mul_left V ((t : ℂ) * I) hu)
  have hA₂ (t : ℝ) : (∫ x : ℝ, A x t) =
      (u : ℂ) ^ (-((t : ℂ) * I)) * Complex.exp (((t : ℂ) * I) ^ 2) := by
    have hm : R t * mellin V ((t : ℂ) * I) = Complex.exp (((t : ℂ) * I) ^ 2) := by
      rw [hV]
      exact sourceThetaReciprocalMellin_mul_symbol hC₀ hA₀ r _ (by simp)
    calc
      _ = R t * ∫ x : ℝ, Complex.exp (((t : ℂ) * I) * (x : ℂ)) * W x := by
        simp only [A, mul_assoc, integral_const_mul]
      _ = _ := by rw [hInner, mul_left_comm, hm]
  calc
    _ = ∫ x : ℝ, sourceThetaGaussianLogKernel C₀ A₀ r x * W x := by
      unfold sourceThetaGaussianSmoothing
      rw [sourceMellin_eq_log]
      simp only [zero_mul, Complex.exp_zero, one_mul, sourceThetaGaussianKernel, Real.log_exp, W]
    _ = c • ∫ x : ℝ, ∫ t : ℝ, A x t := by simp_rw [hA₁, integral_smul]
    _ = c • ∫ t : ℝ, ∫ x : ℝ, A x t := congrArg (fun z : ℂ => c • z) (integral_integral_swap hA)
    _ = c • ∫ t : ℝ, (u : ℂ) ^ (-((t : ℂ) * I)) * Complex.exp (((t : ℂ) * I) ^ 2) := by
      simp_rw [hA₂]
    _ = _ := by
      rw [Complex.real_smul]
      simpa only [Complex.ofReal_zero, zero_add, c] using reflectionGaussian_inverse_mellin hu 0

end
end ArtinMatthews.SourceReflection
