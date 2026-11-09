module

public import ArtinMatthews.SourceThetaReciprocalMellin


set_option backward.privateInPublic true
@[expose] public section

/-! The literal inverse Gaussian smoothing kernel on every vertical
line. Each contour move uses the actual entire multiplier and a proved
Gaussian majorant on the full intervening strip. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Filter Complex VaryingKummerAnalytic
open scoped Topology
noncomputable section

private theorem halfGaussian_horizontal_tendsto_zero (F : ℂ → ℂ) (a b C : ℝ)
    (hbound : ∀ x ∈ uIcc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2) / 2)) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + T * I)) atTop (𝓝 0) := by
  have hnorm (T : ℝ) : ‖∫ x : ℝ in a..b, F ((x : ℂ) + T * I)‖ ≤
      C * Real.exp (-(T ^ 2) / 2) * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hbound x (uIoc_subset_uIcc hx) T)
  have hquad : Tendsto (fun T : ℝ => T ^ 2 / 2) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr (tendsto_pow_atTop (by decide))
  have hexp : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2) / 2)) atTop (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hquad)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hnorm
    (by simpa only [mul_zero, zero_mul] using (hexp.const_mul C).mul_const |b-a|)

/-- Vertical contour translation with the genuine half-Gaussian strip
majorant used for the reciprocal Gamma product. -/
theorem sourceHalfGaussian_verticalIntegral_eq (F : ℂ → ℂ) {a b C : ℝ}
    (hab : a ≤ b) (hF : Differentiable ℂ F)
    (hbound : ∀ x ∈ Icc a b, ∀ y : ℝ,
      ‖F ((x : ℂ) + y * I)‖ ≤ C * Real.exp (-(y ^ 2) / 2)) :
    (∫ y : ℝ, F ((a : ℂ) + y * I)) = ∫ y : ℝ, F ((b : ℂ) + y * I) := by
  have hv (x : ℝ) (hx : x ∈ Icc a b) : Integrable (fun y : ℝ => F ((x : ℂ) + y * I)) := by
    have hc : Continuous (fun y : ℝ => F ((x : ℂ) + y * I)) := hF.continuous.comp (by fun_prop)
    exact (gaussian_half_exp_integrable.const_mul C).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (hbound x hx))
  apply OAI.SevenEighths.Continuation.vertical_integral_eq_of_horizontal_vanish F hab
    hF.differentiableOn (hv a ⟨le_rfl, hab⟩) (hv b ⟨hab, le_rfl⟩)
  · have h := halfGaussian_horizontal_tendsto_zero (fun z => F ((z.re : ℂ) + (-z.im) * I)) a b C (by
      intro x hx y
      have hh := hbound x (by simpa only [uIcc_of_le hab] using hx) (-y)
      simpa using hh)
    simpa using h
  · exact halfGaussian_horizontal_tendsto_zero F a b C (by simpa only [uIcc_of_le hab] using hbound)

def sourceThetaGaussianLogKernelLine (C₀ A₀ : ℝ) (r : ℕ) (σ x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
    sourceThetaReciprocalMellin C₀ A₀ r ((σ : ℂ) + t * I) *
      Complex.exp (((σ : ℂ) + t * I) * (x : ℂ))

def sourceThetaGaussianLogKernel (C₀ A₀ : ℝ) (r : ℕ) : ℝ → ℂ :=
  sourceThetaGaussianLogKernelLine C₀ A₀ r 0

def sourceThetaGaussianKernel (C₀ A₀ : ℝ) (r : ℕ) (T : ℝ) : ℂ :=
  sourceThetaGaussianLogKernel C₀ A₀ r (Real.log T)

private theorem sourceThetaLogKernel_strip (C₀ A₀ : ℝ) (r : ℕ) (a b x : ℝ) :
    ∃ C : ℝ, ∀ q ∈ Icc a b, ∀ t : ℝ,
      ‖sourceThetaReciprocalMellin C₀ A₀ r ((q : ℂ) + t * I) *
        Complex.exp (((q : ℂ) + t * I) * (x : ℂ))‖ ≤ C * Real.exp (-(t ^ 2) / 2) := by
  obtain ⟨D, hD, hDstrip⟩ := sourceThetaReciprocalMellin_strip C₀ A₀ r a b
  let B := max |a| |b|
  refine ⟨D * Real.exp (B * |x|), fun q hq t => ?_⟩
  have hB : |q| ≤ B := abs_le.mpr ⟨
    (neg_le.mp ((neg_le_abs a).trans (le_max_left _ _))).trans hq.1,
    hq.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  have ha : Real.exp (q * x) ≤ Real.exp (B * |x|) := Real.exp_le_exp.mpr
    ((le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hB (abs_nonneg _)))
  have h := hDstrip ((q : ℂ) + t * I) (by simpa using hq)
  have hh : ‖sourceThetaReciprocalMellin C₀ A₀ r ((q : ℂ) + t * I)‖ ≤ D * Real.exp (-(t ^ 2) / 2) := by
    simpa using h
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.add_re, Complex.I_re, zero_mul, add_zero]
  exact (mul_le_mul hh ha (Real.exp_pos _).le (by positivity)).trans_eq (by ring)

theorem sourceThetaGaussianLogKernelLine_eq (C₀ A₀ : ℝ) (r : ℕ) (σ τ x : ℝ) :
    sourceThetaGaussianLogKernelLine C₀ A₀ r σ x = sourceThetaGaussianLogKernelLine C₀ A₀ r τ x := by
  let F (s : ℂ) := sourceThetaReciprocalMellin C₀ A₀ r s * Complex.exp (s * (x : ℂ))
  have hF : Differentiable ℂ F := (sourceThetaReciprocalMellin_entire C₀ A₀ r).mul (by fun_prop)
  have hs (a b : ℝ) (hab : a ≤ b) :
      sourceThetaGaussianLogKernelLine C₀ A₀ r a x = sourceThetaGaussianLogKernelLine C₀ A₀ r b x := by
    obtain ⟨C, hC⟩ := sourceThetaLogKernel_strip C₀ A₀ r a b x
    exact congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z)
      (sourceHalfGaussian_verticalIntegral_eq F hab hF hC)
  rcases le_total σ τ with h | h
  · exact hs σ τ h
  · exact (hs τ σ h).symm

theorem sourceThetaGaussianLogKernel_eq_line (C₀ A₀ : ℝ) (r : ℕ) (σ x : ℝ) :
    sourceThetaGaussianLogKernel C₀ A₀ r x = sourceThetaGaussianLogKernelLine C₀ A₀ r σ x :=
  sourceThetaGaussianLogKernelLine_eq C₀ A₀ r 0 σ x

theorem sourceThetaGaussianKernel_eq_vertical (C₀ A₀ : ℝ) (r : ℕ) (σ : ℝ)
    {T : ℝ} (hT : 0 < T) :
    sourceThetaGaussianKernel C₀ A₀ r T = (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
      sourceThetaReciprocalMellin C₀ A₀ r ((σ : ℂ) + t * I) *
        (T : ℂ) ^ ((σ : ℂ) + t * I) := by
  rw [sourceThetaGaussianKernel, sourceThetaGaussianLogKernel_eq_line C₀ A₀ r σ]
  unfold sourceThetaGaussianLogKernelLine
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hT.ne'), ← Complex.ofReal_log hT.le,
    mul_comm (Real.log T : ℂ)]

theorem sourceThetaGaussianLogKernel_line_bound (C₀ A₀ : ℝ) (r : ℕ) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖sourceThetaGaussianLogKernel C₀ A₀ r x‖ ≤ C * Real.exp (σ * x) := by
  let R (t : ℝ) := sourceThetaReciprocalMellin C₀ A₀ r ((σ : ℂ) + t * I)
  let p := 1 / (2 * Real.pi)
  have hp : 0 ≤ p := one_div_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)
  refine ⟨p * (∫ t : ℝ, ‖R t‖), mul_nonneg hp (integral_nonneg fun _ => norm_nonneg _), fun x => ?_⟩
  rw [sourceThetaGaussianLogKernel_eq_line C₀ A₀ r σ, sourceThetaGaussianLogKernelLine, norm_smul,
    Real.norm_of_nonneg hp]
  have hnorm (t : ℝ) : ‖R t * Complex.exp (((σ : ℂ) + t * I) * (x : ℂ))‖ =
      ‖R t‖ * Real.exp (σ * x) := by
    rw [norm_mul, Complex.norm_exp]
    simp
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hp
  calc
    _ ≤ ∫ t : ℝ, ‖R t * Complex.exp (((σ : ℂ) + t * I) * (x : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp_rw [hnorm, integral_mul_const]

end
end ArtinMatthews.SourceReflection
