module

public import ArtinMatthews.SourceReflectedFourierSeparation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier


set_option backward.privateInPublic true
@[expose] public section

/-! Exact conversion from Mathlib's cycles Fourier transform to the
angular frequency used by the reflected source. The Jacobian is explicit. -/
namespace ArtinMatthews.SourceReflection

open MeasureTheory
open scoped FourierTransform SchwartzMap
noncomputable section

/-- The angular-frequency coefficient, with its exact 1/(2π) density. -/
def sourceReflectedFourierCoefficient (f : 𝓢(ℝ, ℂ)) (τ : ℝ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℝ) • (𝓕 f) ((2 * Real.pi)⁻¹ * τ)

theorem sourceReflectedFourierCoefficient_integrable (f : 𝓢(ℝ, ℂ)) :
    Integrable (sourceReflectedFourierCoefficient f) := by
  have h : (2 * Real.pi : ℝ) ≠ 0 := (mul_pos (by norm_num) Real.pi_pos).ne'
  unfold sourceReflectedFourierCoefficient
  simp_rw [Complex.real_smul]
  exact ((𝓕 f).integrable.comp_mul_left' (inv_ne_zero h)).const_mul _

theorem sourceReflectedFourierCoefficient_norm_integral (f : 𝓢(ℝ, ℂ)) :
    (∫ τ : ℝ, ‖sourceReflectedFourierCoefficient f τ‖) = ∫ ξ : ℝ, ‖(𝓕 f) ξ‖ := by
  let p := 2 * Real.pi
  have hp : 0 < p := mul_pos (by norm_num) Real.pi_pos
  have hnorm (τ : ℝ) : ‖sourceReflectedFourierCoefficient f τ‖ = p⁻¹ * ‖(𝓕 f) (p⁻¹ * τ)‖ := by
    change ‖p⁻¹ • (𝓕 f) (p⁻¹ * τ)‖ = _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  simp_rw [hnorm]
  have hscale := Measure.integral_comp_inv_mul_left (fun ξ : ℝ => ‖(𝓕 f) ξ‖) p
  change (∫ ξ : ℝ, ‖(𝓕 f) (p⁻¹ * ξ)‖) = _ at hscale
  rw [integral_const_mul, hscale, abs_of_pos hp, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hp.ne', one_mul]

theorem sourceReflectedFourierCoefficient_inverse (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    f x = ∫ τ : ℝ, sourceReflectedFourierCoefficient f τ * sourceReflectedFourierPhase τ x := by
  let p := 2 * Real.pi
  have hp : 0 < p := mul_pos (by norm_num) Real.pi_pos
  let F (ξ : ℝ) := (𝓕 f) ξ * sourceReflectedFourierPhase (p * ξ) x
  have hF : (∫ ξ : ℝ, F ξ) = f x := by
    have h := congrFun (f.continuous.fourierInv_fourier_eq f.integrable (𝓕 f).integrable) x
    rw [Real.fourierInv_eq'] at h
    have hphase (ξ : ℝ) : Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) =
        sourceReflectedFourierPhase (p * ξ) x := by
      unfold sourceReflectedFourierPhase
      congr 1
      simp only [RCLike.inner_apply, conj_trivial, p]
      push_cast
      ring
    rw [← h]
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [hphase ξ, smul_eq_mul, ← SchwartzMap.fourier_coe]
    exact mul_comm _ _
  have he (τ : ℝ) : sourceReflectedFourierCoefficient f τ * sourceReflectedFourierPhase τ x =
      p⁻¹ • F (p⁻¹ * τ) := by
    change (p⁻¹ • (𝓕 f) (p⁻¹ * τ)) * _ = _
    rw [show F (p⁻¹ * τ) = (𝓕 f) (p⁻¹ * τ) * sourceReflectedFourierPhase (p * (p⁻¹ * τ)) x from rfl,
      mul_inv_cancel_left₀ hp.ne', Complex.real_smul, Complex.real_smul, mul_assoc]
  simp_rw [he]
  rw [integral_smul, Measure.integral_comp_inv_mul_left F p, abs_of_pos hp, smul_smul,
    inv_mul_cancel₀ hp.ne', one_smul, hF]

end
end ArtinMatthews.SourceReflection
