module

public import ArtinMatthews.SourceThetaGaussianKernel
public import ArtinMatthews.SourceLogMellinCoordinate
public import ArtinMatthews.SourceThetaGaussianMoments
public import ArtinMatthews.SourceThetaIntegralDerivatives
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! Propagation of the actual source03 log derivatives and absolute
sheet bounds through both physical Gaussian convolutions. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Filter ArtinMatthews.SourcePhysical
noncomputable section

def sourceThetaGaussianProfile (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ) (H : ℝ → ℂ) (u : ℝ) : ℂ :=
  mellin (fun T : ℝ => sourceThetaGaussianKernel C₀ A₀ r T * H (u * T ^ τ)) 0

def sourceThetaGaussianLogSmooth (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ) (H : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, sourceThetaGaussianLogKernel C₀ A₀ r y * H (x + τ * y)

def sourceThetaGaussianLogSmoothAbs (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, ‖sourceThetaGaussianLogKernel C₀ A₀ r y‖ * A (x + τ * y)

def sourceThetaGaussianLogMoment (C₀ A₀ : ℝ) (r : ℕ) (β : ℝ) : ℝ :=
  ∫ y : ℝ, ‖sourceThetaGaussianLogKernel C₀ A₀ r y‖ * Real.exp (β * y)

theorem sourceThetaGaussianLogMoment_nonneg (C₀ A₀ : ℝ) (r : ℕ) (β : ℝ) :
    0 ≤ sourceThetaGaussianLogMoment C₀ A₀ r β :=
  integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem sourceThetaGaussianProfile_exp (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ) (H : ℝ → ℂ) (x : ℝ) :
    sourceThetaGaussianProfile C₀ A₀ r τ H (Real.exp x) =
      sourceThetaGaussianLogSmooth C₀ A₀ r τ (fun t => H (Real.exp t)) x := by
  unfold sourceThetaGaussianProfile sourceThetaGaussianLogSmooth
  rw [sourceMellin_eq_log]
  apply integral_congr_ae
  filter_upwards with y
  rw [zero_mul, Complex.exp_zero, one_mul, sourceThetaGaussianKernel, Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.exp_add, mul_comm τ y]

theorem sourceThetaGaussianProfile_reflected (C₀ A₀ : ℝ) (r : ℕ) (H : ℝ → ℂ) (u : ℝ) :
    sourceThetaGaussianProfile C₀ A₀ r (-1) H u =
      mellin (fun T : ℝ => sourceThetaGaussianKernel C₀ A₀ r T * H (u / T)) 0 := by
  simp only [sourceThetaGaussianProfile, Real.rpow_neg_one, div_eq_mul_inv]

theorem sourceThetaGaussianProfile_forward (C₀ A₀ : ℝ) (r : ℕ) (H : ℝ → ℂ) (u : ℝ) :
    sourceThetaGaussianProfile C₀ A₀ r 1 H u =
      mellin (fun T : ℝ => sourceThetaGaussianKernel C₀ A₀ r T * H (u * T)) 0 := by
  simp only [sourceThetaGaussianProfile, Real.rpow_one]

theorem sourceThetaGaussianLogSmoothAbs_weighted (C₀ A₀ : ℝ) (r : ℕ) (τ σ C : ℝ)
    (A : ℝ → ℝ) (hA : Measurable A) (ha : ∀ x, 0 ≤ A x)
    (hb : ∀ x, A x ≤ C * Real.exp (-σ * x)) (x : ℝ) :
    Integrable (fun y : ℝ => ‖sourceThetaGaussianLogKernel C₀ A₀ r y‖ * A (x + τ * y)) ∧
      sourceThetaGaussianLogSmoothAbs C₀ A₀ r τ A x ≤
        (C * sourceThetaGaussianLogMoment C₀ A₀ r (-τ * σ)) * Real.exp (-σ * x) := by
  let K := sourceThetaGaussianLogKernel C₀ A₀ r
  let W (y : ℝ) := ‖K y‖ * Real.exp ((-τ * σ) * y)
  have hW : Integrable W := sourceThetaGaussianLogKernel_weighted_integrable C₀ A₀ r (-τ * σ)
  have hm : Measurable (fun y : ℝ => ‖K y‖ * A (x + τ * y)) :=
    (sourceThetaGaussianLogKernel_continuous C₀ A₀ r).norm.measurable.mul
      (hA.comp (by fun_prop))
  have hpt (y : ℝ) : ‖K y‖ * A (x + τ * y) ≤ (C * Real.exp (-σ * x)) * W y := by
    calc
      _ ≤ ‖K y‖ * (C * Real.exp (-σ * (x + τ * y))) :=
        mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
      _ = _ := by
        dsimp only [W]
        rw [show -σ * (x + τ * y) = -σ * x + (-τ * σ) * y by ring, Real.exp_add]
        ac_rfl
  have hI : Integrable (fun y : ℝ => ‖K y‖ * A (x + τ * y)) :=
    (hW.const_mul (C * Real.exp (-σ * x))).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun y => (Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (ha _))).trans_le (hpt y))
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ y, (C * Real.exp (-σ * x)) * W y := integral_mono hI (hW.const_mul _) hpt
    _ = _ := by
      rw [integral_const_mul]
      change (C * Real.exp (-σ * x)) * sourceThetaGaussianLogMoment C₀ A₀ r (-τ * σ) = _
      ac_rfl

theorem sourceThetaGaussianLogSmooth_norm_le_abs (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ)
    (H : ℝ → ℂ) (hH : Measurable H) (A : ℝ → ℝ) (ha : ∀ x, ‖H x‖ ≤ A x)
    (x : ℝ) (hA : Integrable (fun y : ℝ => ‖sourceThetaGaussianLogKernel C₀ A₀ r y‖ * A (x + τ * y))) :
    Integrable (fun y : ℝ => sourceThetaGaussianLogKernel C₀ A₀ r y * H (x + τ * y)) ∧
      ‖sourceThetaGaussianLogSmooth C₀ A₀ r τ H x‖ ≤ sourceThetaGaussianLogSmoothAbs C₀ A₀ r τ A x := by
  let K := sourceThetaGaussianLogKernel C₀ A₀ r
  have hpt (y : ℝ) : ‖K y * H (x + τ * y)‖ ≤ ‖K y‖ * A (x + τ * y) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (ha _) (norm_nonneg _)
  have hF : Integrable (fun y : ℝ => K y * H (x + τ * y)) :=
    hA.mono' ((sourceThetaGaussianLogKernel_continuous C₀ A₀ r).measurable.mul
      (hH.comp (by fun_prop))).aestronglyMeasurable (Eventually.of_forall hpt)
  exact ⟨hF, (norm_integral_le_integral_norm _).trans (integral_mono hF.norm hA hpt)⟩

theorem sourceThetaGaussianLogSmooth_hasDerivAt (C₀ A₀ : ℝ) (r : ℕ) (τ : ℝ)
    (H H' : ℝ → ℂ) (hH' : Measurable H') (hd : ∀ x, HasDerivAt H (H' x) x)
    (C C' : ℝ) (hb : ∀ x, ‖H x‖ ≤ C) (hb' : ∀ x, ‖H' x‖ ≤ C') (x : ℝ) :
    HasDerivAt (sourceThetaGaussianLogSmooth C₀ A₀ r τ H) (sourceThetaGaussianLogSmooth C₀ A₀ r τ H' x) x := by
  let K := sourceThetaGaussianLogKernel C₀ A₀ r
  have hK : Integrable (fun y : ℝ => ‖K y‖) := by
    simpa only [zero_mul, Real.exp_zero, mul_one, K] using
      sourceThetaGaussianLogKernel_weighted_integrable C₀ A₀ r 0
  have hKm := (sourceThetaGaussianLogKernel_continuous C₀ A₀ r).measurable
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  let F (J : ℝ → ℂ) (t y : ℝ) := K y * J (t + τ * y)
  have hF_meas (J : ℝ → ℂ) (hJ : Measurable J) (t : ℝ) : Measurable (F J t) :=
    hKm.mul (hJ.comp (by fun_prop))
  have hF (t : ℝ) : Integrable (F H t) := by
    refine (hK.const_mul C).mono' (hF_meas H hH.measurable t).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    change ‖K y * H (t + τ * y)‖ ≤ C * ‖K y‖
    rw [norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  refine sourceThetaIntegral_hasDerivAt volume (F H) (F H') hF
    (fun t => (hF_meas H' hH' t).aestronglyMeasurable) (fun t y => ?_)
    (fun y => C' * ‖K y‖) (hK.const_mul _) (fun t y => ?_) x
  · let f (u : ℝ) := u + τ * y
    have hf : HasDerivAt f 1 t := (hasDerivAt_id t).add_const _
    simpa only [F, Function.comp_def, f, one_smul] using ((hd (f t)).scomp t hf).const_mul (K y)
  · change ‖K y * H' (t + τ * y)‖ ≤ C' * ‖K y‖
    rw [norm_mul, mul_comm C']
    exact mul_le_mul_of_nonneg_left (hb' _) (norm_nonneg _)

end
end ArtinMatthews.SourceReflection
