module

public import ArtinMatthews.SpectralPeterssonHeckeProfile
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine Fourier transform of the horizontal Hecke profile has
summable integer samples, uniformly down to regulator zero. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform Topology

namespace ArtinMatthews

private theorem spectralPetersson_fourier_norm_le_integral (f : ℝ → ℂ) (v : ℝ) :
    ‖𝓕 f v‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_real_eq]
  calc
    _ ≤ ∫ x, ‖Real.fourierChar (-(x*v)) • f x‖ := norm_integral_le_integral_norm _
    _ = _ := by simp [Circle.smul_def,norm_mul]

def spectralPeterssonHeckeFourierCost (lam : ℝ) : ℝ :=
  Real.pi+Real.pi*((lam+4)^2+2*lam+8)/(2*Real.pi)^2

theorem spectralPeterssonHeckeFourierCost_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    spectralPeterssonHeckeFourierCost a ≤ spectralPeterssonHeckeFourierCost b := by
  unfold spectralPeterssonHeckeFourierCost
  have h := pow_le_pow_left₀ (show 0 ≤ a+4 by linarith) (show a+4 ≤ b+4 by linarith) 2
  gcongr

theorem spectralPeterssonHeckeFourierCost_pos {lam : ℝ} (hlam : 0 ≤ lam) :
    0 < spectralPeterssonHeckeFourierCost lam := by
  unfold spectralPeterssonHeckeFourierCost
  positivity

theorem spectralPeterssonHeckeProfile_fourier_bound (u lam v : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) (hlam : 0 ≤ lam) :
    ‖𝓕 (spectralPeterssonHeckeProfile u lam) v‖ ≤ spectralPeterssonHeckeFourierCost lam/(1+v^2) := by
  let f := spectralPeterssonHeckeProfile u lam
  let f₁ := spectralPeterssonHeckeProfileFirst u lam
  let f₂ := spectralPeterssonHeckeProfileSecond u lam
  let B := (lam+4)^2+2*lam+8
  let r (x : ℝ) := (1+x^2)⁻¹
  have hr : Integrable r := integrable_inv_one_add_sq
  have hπ : (∫ x, r x) = Real.pi := integral_univ_inv_one_add_sq
  have hfD (x : ℝ) : HasDerivAt f (f₁ x) x := spectralPeterssonHeckeProfile_hasDerivAt u lam x
  have h₁D (x : ℝ) : HasDerivAt f₁ (f₂ x) x := spectralPeterssonHeckeProfileFirst_hasDerivAt u lam x
  have hd : Differentiable ℝ f := fun x => (hfD x).differentiableAt
  have hd₁ : Differentiable ℝ f₁ := fun x => (h₁D x).differentiableAt
  have hf_le (x : ℝ) : ‖f x‖ ≤ r x := spectralPeterssonHeckeProfile_norm_le u lam x hu.1 hlam
  have h₂_le (x : ℝ) : ‖f₂ x‖ ≤ r x*B := spectralPeterssonHeckeProfileSecond_norm_le u lam x hu hlam
  have hf : Integrable f := hr.mono' hd.continuous.aestronglyMeasurable (Eventually.of_forall hf_le)
  have hf₁ : Integrable f₁ := (hr.mul_const (lam+4)).mono' hd₁.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => spectralPeterssonHeckeProfileFirst_norm_le u lam x hu hlam)
  have hf₂ : Integrable f₂ := (hr.mul_const B).mono'
    (spectralPeterssonHeckeProfileSecond_measurable u lam).aestronglyMeasurable (Eventually.of_forall h₂_le)
  have hdF : deriv f = f₁ := funext (fun x => (hfD x).deriv)
  have hdF₁ : deriv f₁ = f₂ := funext (fun x => (h₁D x).deriv)
  have hF₁ := Real.fourier_deriv hf hd (hdF ▸ hf₁)
  have hF₂ := Real.fourier_deriv hf₁ hd₁ (hdF₁ ▸ hf₂)
  rw [hdF] at hF₁
  rw [hdF₁] at hF₂
  have hrelation : 𝓕 f₂ v = ((2*(Real.pi : ℂ)*Complex.I*(v : ℂ))^2)*𝓕 f v := by
    rw [hF₂,hF₁]
    simp only [smul_eq_mul,pow_two]
    ring
  have hbound₀ : ‖𝓕 f v‖ ≤ Real.pi :=
    (spectralPetersson_fourier_norm_le_integral f v).trans ((integral_mono hf.norm hr hf_le).trans_eq hπ)
  have hbound₂ : ‖𝓕 f₂ v‖ ≤ Real.pi*B := by
    apply (spectralPetersson_fourier_norm_le_integral f₂ v).trans
    exact (integral_mono hf₂.norm (hr.mul_const B) h₂_le).trans_eq (by rw [integral_mul_const,hπ])
  rw [hrelation,norm_mul,norm_pow] at hbound₂
  have hfactor : ‖2*(Real.pi : ℂ)*Complex.I*(v : ℂ)‖^2 = (2*Real.pi)^2*v^2 := by
    simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,
      Real.norm_eq_abs,show ‖(2 : ℂ)‖ = 2 by norm_num,mul_pow,sq_abs]
  rw [hfactor] at hbound₂
  have hbound₁ : v^2*‖𝓕 f v‖ ≤ Real.pi*B/(2*Real.pi)^2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hbound₂]
  change ‖𝓕 f v‖ ≤ (Real.pi+Real.pi*B/(2*Real.pi)^2)/(1+v^2)
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [hbound₀,hbound₁]

theorem spectralPeterssonHeckeProfile_fourier_tendsto (lam v : ℝ) (hlam : 0 ≤ lam) :
    Tendsto (fun u => 𝓕 (spectralPeterssonHeckeProfile u lam) v) (𝓝[>] (0 : ℝ))
      (𝓝 (𝓕 (spectralPeterssonHeckeProfile 0 lam) v)) := by
  simp only [Real.fourier_real_eq]
  apply tendsto_integral_filter_of_dominated_convergence (fun x => (1+x^2)⁻¹)
  · apply Eventually.of_forall
    intro u
    have h : Continuous (spectralPeterssonHeckeProfile u lam) :=
      (show Differentiable ℝ _ from fun x =>
        (spectralPeterssonHeckeProfile_hasDerivAt u lam x).differentiableAt).continuous
    exact ((Real.continuous_fourierChar.comp (by fun_prop : Continuous (fun x : ℝ => -(x*v)))).smul h).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with u hu
    apply Eventually.of_forall
    intro x
    rw [Circle.smul_def,norm_smul,Circle.norm_coe,one_mul]
    exact spectralPeterssonHeckeProfile_norm_le u lam x (show 0 < u from hu).le hlam
  · exact integrable_inv_one_add_sq
  · apply Eventually.of_forall
    intro x
    have hu : Continuous (fun u : ℝ => ((1+x^2)^(-u) : ℝ)) :=
      (Real.continuous_const_rpow (by positivity)).comp continuous_neg
    have hcont : Continuous (fun u : ℝ => Real.fourierChar (-(x*v)) • spectralPeterssonHeckeProfile u lam x) := by
      simp only [spectralPeterssonHeckeProfile_eq]
      exact continuous_const.smul (continuous_const.mul (Complex.continuous_ofReal.comp hu))
    exact hcont.continuousAt.continuousWithinAt

end ArtinMatthews
