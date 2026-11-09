module

public import ArtinMatthews.SpectralCoreLocalizationBounds
public import ArtinMatthews.SpectralCoreLocalizationCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The actual localization density is dominated by hyperbolic chart
mass and Dirichlet energy with a constant depending only on the cutoff. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set
open scoped ContDiff SchwartzMap LineDeriv

theorem spectralCoreLocalizationFun_chart_bound
    (φ : SchwartzMap (ℝ × ℝ) ℂ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) {M b : ℝ} (hM : 0 ≤ M)
    (hφ : ∀ p, ‖φ p‖ ≤ M ∧ ‖spectralPlanePartialX φ p‖ ≤ M ∧
      ‖spectralPlanePartialY φ p‖ ≤ M) {p : ℝ × ℝ} (hp : 0 < p.2) (hpb : p.2 ≤ b) :
    ‖spectralCoreLocalizationFun φ F p‖^2+
      (‖spectralPlanePartialX (spectralCoreLocalizationFun φ F) p‖^2+
        ‖spectralPlanePartialY (spectralCoreLocalizationFun φ F) p‖^2) ≤
      (5*M^2*(b^2+1))*(spectralCoreChartEnergy F p/p.2^2) := by
  let U : ℝ := ‖spectralSectionPlane F p‖^2
  let E : ℝ := ‖spectralPlanePartialX (spectralSectionPlane F) p‖^2+
    ‖spectralPlanePartialY (spectralSectionPlane F) p‖^2
  have hU : 0 ≤ U := sq_nonneg _
  have hE : 0 ≤ E := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hy2 : 0 < p.2^2 := sq_pos_of_pos hp
  have hband : p.2^2 ≤ b^2 := pow_le_pow_left₀ hp.le hpb 2
  have hmass : U ≤ b^2*(U/p.2^2) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hy2).mpr
    nlinarith [mul_le_mul_of_nonneg_left hband hU]
  have hweight : 0 ≤ U/p.2^2 := div_nonneg hU hy2.le
  have hc0 : 5*M^2*b^2 ≤ 5*M^2*(b^2+1) := by nlinarith [sq_nonneg M]
  have hc1 : 2*M^2 ≤ 5*M^2*(b^2+1) := by
    nlinarith [sq_nonneg M, mul_nonneg (sq_nonneg M) (sq_nonneg b)]
  have henergy : spectralCoreChartEnergy F p = U+p.2^2*E := by
    rw [spectralCoreChartEnergy, spectralSectionPlane_energy F hF hp]
  have he : (U+p.2^2*E)/p.2^2 = U/p.2^2+E := by field_simp
  calc
    _ ≤ 5*M^2*U+2*M^2*E := spectralCoreLocalizationFun_pointwise_energy φ F hF hM hφ hp
    _ ≤ 5*M^2*(b^2*(U/p.2^2))+2*M^2*E :=
      add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity)) le_rfl
    _ = (5*M^2*b^2)*(U/p.2^2)+(2*M^2)*E := by ring
    _ ≤ (5*M^2*(b^2+1))*(U/p.2^2)+(5*M^2*(b^2+1))*E :=
      add_le_add (mul_le_mul_of_nonneg_right hc0 hweight) (mul_le_mul_of_nonneg_right hc1 hE)
    _ = _ := by rw [henergy, he]; ring

def spectralPlaneH1Density (G : SchwartzMap (ℝ × ℝ) ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖G p‖^2+(‖spectralPlanePartialX G p‖^2+‖spectralPlanePartialY G p‖^2)

theorem spectralPlaneH1Density_integrable (G : SchwartzMap (ℝ × ℝ) ℂ)
    (hc : HasCompactSupport (G : ℝ × ℝ → ℂ)) : Integrable (spectralPlaneH1Density G) := by
  have hx : HasCompactSupport (fun p => fderiv ℝ (G : ℝ × ℝ → ℂ) p ((1,0) : ℝ × ℝ)) :=
    hc.fderiv_apply ℝ _
  have hy : HasCompactSupport (fun p => fderiv ℝ (G : ℝ × ℝ → ℂ) p ((0,1) : ℝ × ℝ)) :=
    hc.fderiv_apply ℝ _
  have hdx : HasCompactSupport (fun p => (∂_{((1,0) : ℝ × ℝ)} G) p) := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hx
  have hdy : HasCompactSupport (fun p => (∂_{((0,1) : ℝ × ℝ)} G) p) := by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hy
  have hm := spectral_plane_normsq_integrable G.continuous hc
  have hmx := spectral_plane_normsq_integrable (∂_{((1,0) : ℝ × ℝ)} G).continuous hdx
  have hmy := spectral_plane_normsq_integrable (∂_{((0,1) : ℝ × ℝ)} G).continuous hdy
  convert hm.add (hmx.add hmy) using 1
  funext p
  simp only [spectralPlaneH1Density, spectralPlanePartialX_schwartz,
    spectralPlanePartialY_schwartz, Pi.add_apply]

theorem spectralPlaneH1Density_eq_zero {G : SchwartzMap (ℝ × ℝ) ℂ}
    {S : Set (ℝ × ℝ)} (hG : tsupport G ⊆ S) {p : ℝ × ℝ} (hp : p ∉ S) :
    spectralPlaneH1Density G p = 0 := by
  have hnot : p ∉ tsupport G := fun hh => hp (hG hh)
  have hz : G p = 0 := by
    by_contra hh
    exact hnot (subset_tsupport _ hh)
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
  rw [spectralPlaneH1Density, hz, spectralPlanePartialX_eq_fderiv G.differentiableAt,
    spectralPlanePartialY_eq_fderiv G.differentiableAt, hd]
  simp

end
end ArtinMatthews
