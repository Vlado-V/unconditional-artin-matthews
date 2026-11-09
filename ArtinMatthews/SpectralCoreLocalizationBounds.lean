module

public import ArtinMatthews.SpectralCoreLocalizationDerivatives


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed-cutoff bounds for the actual localized mass and first derivatives. -/

namespace ArtinMatthews
noncomputable section

open Set
open scoped SchwartzMap LineDeriv ContDiff

theorem spectral_cutoff_coordinate_bound (φ : SchwartzMap (ℝ × ℝ) ℂ) :
    ∃ M : ℝ, 0 < M ∧ ∀ p, ‖φ p‖ ≤ M ∧
      ‖spectralPlanePartialX φ p‖ ≤ M ∧ ‖spectralPlanePartialY φ p‖ ≤ M := by
  let dx : SchwartzMap (ℝ × ℝ) ℂ := ∂_{((1,0) : ℝ × ℝ)} φ
  let dy : SchwartzMap (ℝ × ℝ) ℂ := ∂_{((0,1) : ℝ × ℝ)} φ
  let M0 : ℝ := SchwartzMap.seminorm ℝ 0 0 φ
  let Mx : ℝ := SchwartzMap.seminorm ℝ 0 0 dx
  let My : ℝ := SchwartzMap.seminorm ℝ 0 0 dy
  have h0 : 0 ≤ M0 := by dsimp [M0]; positivity
  have hx : 0 ≤ Mx := by dsimp [Mx]; positivity
  have hy : 0 ≤ My := by dsimp [My]; positivity
  refine ⟨1+M0+Mx+My, by linarith, fun p => ?_⟩
  have hp0 : ‖φ p‖ ≤ M0 := SchwartzMap.norm_le_seminorm ℝ φ p
  have hpx : ‖spectralPlanePartialX φ p‖ ≤ Mx := by
    rw [spectralPlanePartialX_schwartz]
    exact SchwartzMap.norm_le_seminorm ℝ dx p
  have hpy : ‖spectralPlanePartialY φ p‖ ≤ My := by
    rw [spectralPlanePartialY_schwartz]
    exact SchwartzMap.norm_le_seminorm ℝ dy p
  exact ⟨by linarith, by linarith, by linarith⟩

lemma spectral_norm_add_sq_le (z w : ℂ) :
    ‖z+w‖^2 ≤ 2*(‖z‖^2+‖w‖^2) := by
  have hh := pow_le_pow_left₀ (norm_nonneg (z+w)) (norm_add_le z w) 2
  nlinarith [sq_nonneg (‖z‖-‖w‖)]

theorem spectralCoreLocalizationFun_pointwise_energy
    (φ : SchwartzMap (ℝ × ℝ) ℂ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) {M : ℝ} (_hM : 0 ≤ M)
    (hφ : ∀ p, ‖φ p‖ ≤ M ∧ ‖spectralPlanePartialX φ p‖ ≤ M ∧
      ‖spectralPlanePartialY φ p‖ ≤ M) {p : ℝ × ℝ} (hp : 0 < p.2) :
    ‖spectralCoreLocalizationFun φ F p‖^2+
      (‖spectralPlanePartialX (spectralCoreLocalizationFun φ F) p‖^2+
        ‖spectralPlanePartialY (spectralCoreLocalizationFun φ F) p‖^2) ≤
      5*M^2*‖spectralSectionPlane F p‖^2+
        2*M^2*(‖spectralPlanePartialX (spectralSectionPlane F) p‖^2+
          ‖spectralPlanePartialY (spectralSectionPlane F) p‖^2) := by
  have hf : DifferentiableAt ℝ (spectralSectionPlane F) p :=
    (spectralSectionPlane_contDiffAt F hF hp).differentiableAt (by simp)
  have h0 := pow_le_pow_left₀ (norm_nonneg (φ p)) (hφ p).1 2
  have hx := pow_le_pow_left₀ (norm_nonneg (spectralPlanePartialX φ p)) (hφ p).2.1 2
  have hy := pow_le_pow_left₀ (norm_nonneg (spectralPlanePartialY φ p)) (hφ p).2.2 2
  have hg0 : ‖spectralCoreLocalizationFun φ F p‖^2 ≤ M^2*‖spectralSectionPlane F p‖^2 := by
    rw [spectralCoreLocalizationFun, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right h0 (sq_nonneg _)
  have hgx : ‖spectralPlanePartialX (spectralCoreLocalizationFun φ F) p‖^2 ≤
      2*M^2*‖spectralSectionPlane F p‖^2+
        2*M^2*‖spectralPlanePartialX (spectralSectionPlane F) p‖^2 := by
    change ‖spectralPlanePartialX (fun q => φ q*spectralSectionPlane F q) p‖^2 ≤ _
    rw [spectralPlanePartialX_mul φ.differentiableAt hf]
    have hh := spectral_norm_add_sq_le
      (spectralPlanePartialX φ p*spectralSectionPlane F p)
      (φ p*spectralPlanePartialX (spectralSectionPlane F) p)
    simp only [norm_mul, mul_pow] at hh
    nlinarith [mul_le_mul_of_nonneg_right hx (sq_nonneg ‖spectralSectionPlane F p‖),
      mul_le_mul_of_nonneg_right h0 (sq_nonneg ‖spectralPlanePartialX (spectralSectionPlane F) p‖)]
  have hgy : ‖spectralPlanePartialY (spectralCoreLocalizationFun φ F) p‖^2 ≤
      2*M^2*‖spectralSectionPlane F p‖^2+
        2*M^2*‖spectralPlanePartialY (spectralSectionPlane F) p‖^2 := by
    change ‖spectralPlanePartialY (fun q => φ q*spectralSectionPlane F q) p‖^2 ≤ _
    rw [spectralPlanePartialY_mul φ.differentiableAt hf]
    have hh := spectral_norm_add_sq_le
      (spectralPlanePartialY φ p*spectralSectionPlane F p)
      (φ p*spectralPlanePartialY (spectralSectionPlane F) p)
    simp only [norm_mul, mul_pow] at hh
    nlinarith [mul_le_mul_of_nonneg_right hy (sq_nonneg ‖spectralSectionPlane F p‖),
      mul_le_mul_of_nonneg_right h0 (sq_nonneg ‖spectralPlanePartialY (spectralSectionPlane F) p‖)]
  linarith

end
end ArtinMatthews
