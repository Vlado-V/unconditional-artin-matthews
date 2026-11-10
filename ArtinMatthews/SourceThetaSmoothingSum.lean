module

public import ArtinMatthews.SourceThetaProfileSmoothing
public import ArtinMatthews.SourceThetaGaussianMoments
public import Mathlib.Data.Nat.Factorial.DoubleFactorial


set_option backward.privateInPublic true
@[expose] public section

/-! The source03 absolute-sum bound and interchange. The real
parameters are log u and log x_i, so every positive scale is covered. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory Filter
noncomputable section

variable {ι : Type*} [Countable ι]
variable (C₀ A₀ : ℝ) (r : ℕ) (τ σ C x : ℝ)
variable (a : ι → ℂ) (v : ι → ℝ) (A : ι → ℝ → ℝ)

local notation "Klog" => sourceThetaGaussianLogKernel C₀ A₀ r
local notation "p" => (fun i => ‖a i‖ * Real.exp (-σ * v i))
local notation "b" => (fun i y => ‖a i‖ * A i (x + v i + τ * y))

omit [Countable ι] in
private theorem thetaAbsSum_term_bound (hb : ∀ i t, A i t ≤ C * Real.exp (-σ * t)) (i : ι) (y : ℝ) :
    b i y ≤ ((C * Real.exp (-σ * x)) * Real.exp ((-τ * σ) * y)) * p i := by
  calc
    _ ≤ ‖a i‖ * (C * Real.exp (-σ * (x + v i + τ * y))) :=
      mul_le_mul_of_nonneg_left (hb i _) (norm_nonneg _)
    _ = _ := by
      rw [show -σ * (x + v i + τ * y) = -σ * x + -σ * v i + (-τ * σ) * y by ring,
        Real.exp_add, Real.exp_add]
      ring

theorem sourceThetaGaussianLogAbsSum_bound (hA : ∀ i, Measurable (A i))
    (ha : ∀ i t, 0 ≤ A i t) (hb : ∀ i t, A i t ≤ C * Real.exp (-σ * t))
    (hs : Summable p) :
    (∀ y, Summable (fun i => b i y)) ∧
    Integrable (fun y : ℝ => ‖Klog y‖ * (∑' i, b i y)) ∧
      (∫ y : ℝ, ‖Klog y‖ * (∑' i, b i y)) ≤
        C * Real.exp (-σ * x) * sourceThetaGaussianLogMoment C₀ A₀ r (-τ * σ) * (∑' i, p i) := by
  let W (y : ℝ) := ‖Klog y‖ * Real.exp ((-τ * σ) * y)
  let M := C * Real.exp (-σ * x) * (∑' i, p i)
  have hW : Integrable W := sourceThetaGaussianLogKernel_weighted_integrable C₀ A₀ r (-τ * σ)
  have hn (i : ι) (y : ℝ) : 0 ≤ b i y := mul_nonneg (norm_nonneg _) (ha i _)
  have hsum (y : ℝ) : Summable (fun i => b i y) :=
    Summable.of_nonneg_of_le (fun i => hn i y)
      (fun i => thetaAbsSum_term_bound τ σ C x a v A hb i y) (hs.mul_left _)
  have hmeas : Measurable (fun y : ℝ => ‖Klog y‖ * (∑' i, b i y)) :=
    (sourceThetaGaussianLogKernel_continuous C₀ A₀ r).norm.measurable.mul
      (Measurable.tsum fun i => (hA i).comp (by fun_prop) |>.const_mul _)
  have hpt (y : ℝ) : ‖Klog y‖ * (∑' i, b i y) ≤ M * W y := by
    have h := Summable.tsum_le_tsum (fun i => thetaAbsSum_term_bound τ σ C x a v A hb i y)
      (hsum y) (hs.mul_left ((C * Real.exp (-σ * x)) * Real.exp ((-τ * σ) * y)))
    rw [tsum_mul_left] at h
    exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (by dsimp only [M, W]; ac_rfl)
  have hI : Integrable (fun y : ℝ => ‖Klog y‖ * (∑' i, b i y)) :=
    (hW.const_mul M).mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun y =>
      (Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (tsum_nonneg fun i => hn i y))).trans_le (hpt y))
  refine ⟨hsum, hI, ?_⟩
  calc
    _ ≤ ∫ y, M * W y := integral_mono hI (hW.const_mul _) hpt
    _ = _ := by
      rw [integral_const_mul]
      change M * sourceThetaGaussianLogMoment C₀ A₀ r (-τ * σ) = _
      dsimp only [M]
      ac_rfl

/-- Absolute summability of the actual weighted source expansion permits
termwise Gaussian smoothing with both scale signs. -/
theorem sourceThetaGaussianLogSmooth_sum_integral (hA : ∀ i, Measurable (A i))
    (ha : ∀ i t, 0 ≤ A i t) (hb : ∀ i t, A i t ≤ C * Real.exp (-σ * t))
    (hs : Summable p) (H : ι → ℝ → ℂ) (hH : ∀ i, Measurable (H i))
    (hHA : ∀ i t, ‖H i t‖ ≤ A i t) :
    (∫ y : ℝ, Klog y * (∑' i, a i * H i (x + v i + τ * y))) =
      ∑' i, a i * sourceThetaGaussianLogSmooth C₀ A₀ r τ (H i) (x + v i) := by
  obtain ⟨hSum, hI, _⟩ := sourceThetaGaussianLogAbsSum_bound C₀ A₀ r τ σ C x a v A hA ha hb hs
  let F (i : ι) (y : ℝ) := Klog y * (a i * H i (x + v i + τ * y))
  have hF (i : ι) : Measurable (F i) :=
    (sourceThetaGaussianLogKernel_continuous C₀ A₀ r).measurable.mul
      ((hH i).comp (by fun_prop) |>.const_mul _)
  have hF_le (i : ι) (y : ℝ) : ‖F i y‖ ≤ ‖Klog y‖ * b i y := by
    dsimp only [F]
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hHA i _) (norm_nonneg _)) (norm_nonneg _)
  have hI' : Integrable (fun y : ℝ => ∑' i, ‖Klog y‖ * b i y) := by
    simpa only [tsum_mul_left] using hI
  have hLim (y : ℝ) :
      HasSum (fun i => F i y) (Klog y * (∑' i, a i * H i (x + v i + τ * y))) := by
    have hh : Summable (fun i => a i * H i (x + v i + τ * y)) := by
      apply (Summable.of_nonneg_of_le (fun i => norm_nonneg (a i * H i (x + v i + τ * y)))
        (fun i => ?_) (hSum y)).of_norm
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hHA i _) (norm_nonneg _)
    exact hh.hasSum.mul_left _
  have h := hasSum_integral_of_dominated_convergence (μ := volume)
    (fun i y => ‖Klog y‖ * b i y) (fun i => (hF i).aestronglyMeasurable)
    (fun i => Eventually.of_forall (hF_le i)) (Eventually.of_forall fun y => (hSum y).mul_left _)
    hI' (Eventually.of_forall hLim)
  refine h.tsum_eq.symm.trans ?_
  apply tsum_congr
  intro i
  unfold sourceThetaGaussianLogSmooth
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  dsimp only [F]
  ac_rfl

end
end ArtinMatthews.SourceReflection
