module

public import ArtinMatthews.SpectralJForwardRealSmooth
public import ArtinMatthews.SpectralJForwardStripRapid
public import ArtinMatthews.SpectralKLDirectDefinitions
public import ArtinMatthews.SpectralKLWeightedMeasures
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic.GCongr


set_option backward.privateInPublic true
@[expose] public section

/-! Exact real-axis inverse data for the actual forward J spectral weight.
The KL density and cosh factor give polynomial, integrable domination. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped ContDiff

namespace ArtinMatthews

theorem spectralJForwardSpectralWeight_norm_real (f : ℝ → ℂ) (t : ℝ) :
    ‖spectralJForwardSpectralWeight f (t : ℂ)‖ =
      (Real.pi/Real.cosh (Real.pi*t))*‖spectralJForwardTransform f (t : ℂ)‖ := by
  rw [spectralJForwardSpectralWeight, ← Complex.ofReal_mul, ← Complex.ofReal_cosh]
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
    abs_of_pos (Real.cosh_pos (Real.pi*t))]

theorem spectralJForwardSpectralWeight_real_directRapid (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    SpectralKLDirectRapid (fun t : ℝ => spectralJForwardSpectralWeight f (t : ℂ)) := by
  intro N
  obtain ⟨C,hC,hb⟩ := spectralJForwardTransform_real_rapid f hf hc hp (2*N)
  refine ⟨2*Real.pi*C,by positivity,?_⟩
  intro t
  let T := 1+|t|
  let a := Real.pi*|t|
  let W := Real.cosh (Real.pi*t)
  have hT : 0 < T := by dsimp [T]; positivity
  have ha : 0 ≤ a := mul_nonneg Real.pi_pos.le (abs_nonneg _)
  have hW : 0 < W := Real.cosh_pos _
  have haAbs : a = |Real.pi*t| := by dsimp [a]; rw [abs_mul,abs_of_pos Real.pi_pos]
  have he : Real.exp a ≤ 2*W := by
    dsimp only [W]
    rw [← Real.cosh_abs (Real.pi*t), ← haAbs, Real.cosh_eq]
    linarith only [Real.exp_pos (-a)]
  have he' : Real.exp (a/2) ≤ 2*W :=
    (Real.exp_le_exp.mpr (by linarith only [ha])).trans he
  have hfct : Real.exp (a/2)*(Real.pi/W) ≤ 2*Real.pi := by
    calc
      _ = (Real.exp (a/2)*Real.pi)/W := by ring
      _ ≤ (2*W*Real.pi)/W := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right he' Real.pi_pos.le) hW.le
      _ = _ := by field_simp [hW.ne'] <;> ring
  have hU : 1+t^2 ≤ T^2 := by
    dsimp only [T]
    nlinarith only [sq_abs t,abs_nonneg t]
  have hP := pow_le_pow_left₀ (by positivity : 0 ≤ 1+t^2) hU N
  rw [← pow_mul] at hP
  have hb' : T^(2*N)*‖spectralJForwardTransform f (t : ℂ)‖ ≤ C := by
    rw [mul_comm]
    exact (le_div_iff₀ (pow_pos hT _)).mp (hb t)
  have hBT : (1+t^2)^N*‖spectralJForwardTransform f (t : ℂ)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans hb'
  change (1+t^2)^N*Real.exp (a/2)*‖spectralJForwardSpectralWeight f (t : ℂ)‖ ≤ _
  rw [spectralJForwardSpectralWeight_norm_real]
  change (1+t^2)^N*Real.exp (a/2)*((Real.pi/W)*‖spectralJForwardTransform f (t : ℂ)‖) ≤ _
  calc
    _ = ((1+t^2)^N*‖spectralJForwardTransform f (t : ℂ)‖)*(Real.exp (a/2)*(Real.pi/W)) := by ring
    _ ≤ C*(2*Real.pi) := mul_le_mul hBT hfct (by positivity) hC
    _ = _ := by ring

theorem spectralJForwardSpectralWeight_weighted_integrable (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (C : ℝ) (hC : 0 ≤ C) :
    Integrable (fun t : ℝ => ‖spectralJForwardSpectralWeight f (t : ℂ)‖*(1+C/t))
      spectralKLSpectralMeasure := by
  let H (t : ℝ) := spectralJForwardSpectralWeight f (t : ℂ)
  let B (t : ℝ) := spectralJForwardTransform f (t : ℂ)
  let w := spectralKLPlancherelWeight
  have hW (t : ℝ) (ht : 0 < t) : 0 ≤ w t := (spectralKLPlancherelWeight_pos ht).le
  have hH : Continuous H := (spectralJForwardSpectralWeight_real_contDiff f hf.continuous hc hp).continuous
  have hCont : Measurable (fun t : ℝ => 1+C/t) := by fun_prop
  have hm : AEStronglyMeasurable (fun t => w t*(‖H t‖*(1+C/t)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (spectralKLPlancherelWeight_continuous.measurable.mul (hH.norm.measurable.mul hCont)).aestronglyMeasurable
  change Integrable (fun t : ℝ => ‖H t‖*(1+C/t)) (spectralKLPositiveWeightMeasure w)
  apply (spectralKLPositiveWeightMeasure_integrable_iff w (fun t => ‖H t‖*(1+C/t))
    spectralKLPlancherelWeight_continuous.measurable hW).mpr
  obtain ⟨M,hM,hB⟩ := spectralJForwardTransform_real_rapid f hf hc hp 3
  let R := (2/Real.pi)*(1+C)*M
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply (integrable_inv_one_add_sq.const_mul R).restrict.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  have hcosh : 0 < Real.cosh (Real.pi*t) := Real.cosh_pos _
  have htanh : Real.sinh (Real.pi*t)/Real.cosh (Real.pi*t) ≤ 1 :=
    (div_le_one₀ hcosh).mpr (Real.sinh_lt_cosh (Real.pi*t)).le
  have hBt : ‖B t‖ ≤ M/(1+t)^3 := by simpa only [B,abs_of_pos ht] using hB t
  have hLin : t+C ≤ (1+C)*(1+t) := by nlinarith only [mul_nonneg hC ht.le]
  rw [Real.norm_of_nonneg (mul_nonneg (hW t ht) (mul_nonneg (norm_nonneg _)
    (by positivity : 0 ≤ 1+C/t)))]
  have hNorm : ‖H t‖ = (Real.pi/Real.cosh (Real.pi*t))*‖B t‖ :=
    spectralJForwardSpectralWeight_norm_real f t
  rw [hNorm]
  calc
    _ = (2/Real.pi)*(t+C)*(Real.sinh (Real.pi*t)/Real.cosh (Real.pi*t))*‖B t‖ := by
      dsimp only [w,spectralKLPlancherelWeight]
      field_simp [Real.pi_ne_zero,ht.ne',hcosh.ne'] <;> ring
    _ ≤ (2/Real.pi)*(t+C)*‖B t‖ := by
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left htanh (by positivity)).trans_eq (mul_one _)) (norm_nonneg _)
    _ ≤ (2/Real.pi)*((1+C)*(1+t))*(M/(1+t)^3) := by gcongr
    _ = R/(1+t)^2 := by
      dsimp only [R]
      field_simp [show 1+t ≠ 0 by positivity] <;> ring
    _ ≤ R/(1+t^2) := div_le_div_of_nonneg_left hR (by positivity) (by nlinarith only [ht])
    _ = _ := div_eq_mul_inv _ _

theorem spectralJForwardSpectralWeight_weber_integrable (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    Integrable (fun t : ℝ => ‖spectralJForwardSpectralWeight f (t : ℂ)‖*
      (1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/t)) spectralKLSpectralMeasure :=
  spectralJForwardSpectralWeight_weighted_integrable f hf hc hp _ (by positivity)

end ArtinMatthews
