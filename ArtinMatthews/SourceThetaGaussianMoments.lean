module

public import ArtinMatthews.SourceThetaGaussianKernel
public import ArtinMatthews.SourceLogMellinCoordinate
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! Every real Mellin moment of the genuine inverse kernel is absolutely
integrable. The two vertical lines are chosen after the moment exponent. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Set Filter Complex SourcePhysical
open scoped Topology
noncomputable section

theorem sourceThetaGaussianLogKernel_continuous (C₀ A₀ : ℝ) (r : ℕ) :
    Continuous (sourceThetaGaussianLogKernel C₀ A₀ r) := by
  let R (t : ℝ) := sourceThetaReciprocalMellin C₀ A₀ r ((0 : ℂ) + t * I)
  let F (x t : ℝ) := R t * Complex.exp (((0 : ℂ) + t * I) * (x : ℂ))
  have hR : Integrable R := sourceThetaReciprocalMellin_verticalIntegrable C₀ A₀ r 0
  have hRc : Continuous R := (sourceThetaReciprocalMellin_entire C₀ A₀ r).continuous.comp (by fun_prop)
  have hF (x : ℝ) : Continuous (F x) := hRc.mul (by fun_prop :
    Continuous (fun t : ℝ => Complex.exp (((0 : ℂ) + t * I) * (x : ℂ))))
  have hnorm (x t : ℝ) : ‖F x t‖ = ‖R t‖ := by
    dsimp only [F]
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.mul_re]
  have h := continuous_of_dominated (μ := volume) (F := F) (bound := fun t => ‖R t‖)
    (fun x => (hF x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (fun t => (hnorm x t).le)) hR.norm
    (Filter.Eventually.of_forall fun t => by dsimp only [F]; fun_prop)
  exact h.const_smul (1 / (2 * Real.pi) : ℝ)

private theorem exp_neg_abs_le_cauchy (x : ℝ) : Real.exp (-|x|) ≤ 4 * (1 + x ^ 2)⁻¹ := by
  have h₁ := Real.add_one_le_exp (|x| / 2)
  have h₂ : 1 + |x| ≤ 2 * Real.exp (|x| / 2) := by linarith
  have hs : (1 + |x|) ^ 2 ≤ (2 * Real.exp (|x| / 2)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr h₂
  have hscale : ((2 : ℕ) : ℝ) * (|x| / 2) = |x| := by push_cast; ring
  rw [mul_pow, ← Real.exp_nat_mul, hscale] at hs
  have h : 1 + x ^ 2 ≤ 4 * Real.exp |x| := by nlinarith [abs_nonneg x, sq_abs x]
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)).mpr
  calc
    _ ≤ (Real.exp |x|)⁻¹ * (4 * Real.exp |x|) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Real.exp_pos _).le)
    _ = 4 := by field_simp

theorem sourceThetaGaussianLogKernel_weighted_integrable (C₀ A₀ : ℝ) (r : ℕ) (β : ℝ) :
    Integrable (fun x : ℝ => ‖sourceThetaGaussianLogKernel C₀ A₀ r x‖ * Real.exp (β * x)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := sourceThetaGaussianLogKernel_line_bound C₀ A₀ r (1 - β)
  obtain ⟨C₂, hC₂, h₂⟩ := sourceThetaGaussianLogKernel_line_bound C₀ A₀ r (-1 - β)
  let C := max C₁ C₂
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  have hcont : Continuous (fun x : ℝ => ‖sourceThetaGaussianLogKernel C₀ A₀ r x‖ * Real.exp (β * x)) :=
    (sourceThetaGaussianLogKernel_continuous C₀ A₀ r).norm.mul (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul (4 * C)).mono' hcont.aestronglyMeasurable
  filter_upwards [] with x
  change ‖‖sourceThetaGaussianLogKernel C₀ A₀ r x‖ * Real.exp (β * x)‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  have hpt : ‖sourceThetaGaussianLogKernel C₀ A₀ r x‖ * Real.exp (β * x) ≤ C * Real.exp (-|x|) := by
    rcases le_total x 0 with hx | hx
    · calc
        _ ≤ (C₁ * Real.exp ((1 - β) * x)) * Real.exp (β * x) :=
          mul_le_mul_of_nonneg_right (h₁ x) (Real.exp_pos _).le
        _ = C₁ * Real.exp (-|x|) := by
          rw [mul_assoc, ← Real.exp_add, abs_of_nonpos hx, neg_neg]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    · calc
        _ ≤ (C₂ * Real.exp ((-1 - β) * x)) * Real.exp (β * x) :=
          mul_le_mul_of_nonneg_right (h₂ x) (Real.exp_pos _).le
        _ = C₂ * Real.exp (-|x|) := by
          rw [mul_assoc, ← Real.exp_add, abs_of_nonneg hx]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  exact hpt.trans ((mul_le_mul_of_nonneg_left (exp_neg_abs_le_cauchy x) hC).trans_eq (by ring))

theorem sourceThetaGaussianKernel_mellinConvergent (C₀ A₀ : ℝ) (r : ℕ) (s : ℂ) :
    MellinConvergent (sourceThetaGaussianKernel C₀ A₀ r) s := by
  rw [sourceMellinConvergent_iff_log]
  have hc : Continuous (fun x : ℝ => Complex.exp (s * (x : ℂ)) * sourceThetaGaussianLogKernel C₀ A₀ r x) :=
    (by fun_prop : Continuous (fun x : ℝ => Complex.exp (s * (x : ℂ)))).mul
      (sourceThetaGaussianLogKernel_continuous C₀ A₀ r)
  simp only [sourceThetaGaussianKernel, Real.log_exp]
  apply (sourceThetaGaussianLogKernel_weighted_integrable C₀ A₀ r s.re).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  change ‖Complex.exp (s * (x : ℂ)) * sourceThetaGaussianLogKernel C₀ A₀ r x‖ ≤ _
  rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_comm]

/-- The literal absolute Mellin moment with measure dT/T is finite. -/
theorem sourceThetaGaussianKernel_absMoment (C₀ A₀ : ℝ) (r : ℕ) (β : ℝ) :
    IntegrableOn (fun T : ℝ => ‖sourceThetaGaussianKernel C₀ A₀ r T‖ * T ^ (β - 1)) (Ioi 0) := by
  have hi := (sourceThetaGaussianKernel_mellinConvergent C₀ A₀ r (β : ℂ)).norm
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mp hi
  intro T hT
  change ‖(T : ℂ) ^ ((β : ℂ) - 1) • sourceThetaGaussianKernel C₀ A₀ r T‖ =
    ‖sourceThetaGaussianKernel C₀ A₀ r T‖ * T ^ (β - 1)
  rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hT, Complex.sub_re, Complex.ofReal_re,
    Complex.one_re, mul_comm]

end
end ArtinMatthews.SourceReflection
