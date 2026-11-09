module

public import ArtinMatthews.SpectralPeterssonPhysicalNorm
public import ArtinMatthews.SpectralPeterssonHilbert


set_option backward.privateInPublic true
@[expose] public section

/-! Cauchy--Schwarz for the literal physical Petersson integrals. -/
noncomputable section
open MeasureTheory UpperHalfPlane
open scoped InnerProductSpace

namespace ArtinMatthews

theorem spectralPeterssonHilbertProfile_norm_sq (k : ℕ) (F : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) :
    ‖spectralPeterssonHilbertProfile k F z‖^2 = ‖F z‖^2*z.im^k := by
  rw [spectralPeterssonHilbertProfile_norm,spectralPeterssonWeightedNorm_sq,spectralPetersson_self_pair,
    Complex.norm_real,Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg z.im_pos.le _))]

theorem spectralPeterssonHilbertProfile_memLp_of_integrable (N k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : Measurable F)
    (hI : IntegrableOn (fun z => ‖F z‖^2*z.im^k) (gamma0InteriorRegion N)) :
    MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)) := by
  have hm : Measurable (spectralPeterssonHilbertProfile k F) := by
    unfold spectralPeterssonHilbertProfile
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [spectralPeterssonHilbertProfile_norm_sq] using! hI

theorem gamma0PeterssonHilbert_norm_sq_integral (N k : ℕ) (F : UpperHalfPlane → ℂ)
    (hF : MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N))) :
    ‖hF.toLp (spectralPeterssonHilbertProfile k F)‖^2 =
      ∫ z in gamma0InteriorRegion N, ‖F z‖^2*z.im^k := by
  rw [gamma0PeterssonHilbert_diagonal_norm]
  have he : gamma0PeterssonInner N k F F =
      ((∫ z in gamma0InteriorRegion N, ‖F z‖^2*z.im^k : ℝ) : ℂ) := by
    simp only [gamma0PeterssonInner,spectralPetersson_self_pair,integral_complex_ofReal]
  rw [he,Complex.ofReal_re]

theorem gamma0PeterssonPhysical_cauchy (N k : ℕ) (F G : UpperHalfPlane → ℂ)
    (hF : MemLp (spectralPeterssonHilbertProfile k F) 2 (volume.restrict (gamma0InteriorRegion N)))
    (hG : MemLp (spectralPeterssonHilbertProfile k G) 2 (volume.restrict (gamma0InteriorRegion N))) :
    ‖gamma0PeterssonInner N k F G‖^2 ≤
      (∫ z in gamma0InteriorRegion N, ‖F z‖^2*z.im^k)*
      (∫ z in gamma0InteriorRegion N, ‖G z‖^2*z.im^k) := by
  have h := norm_inner_le_norm (𝕜 := ℂ)
    (hF.toLp (spectralPeterssonHilbertProfile k F)) (hG.toLp (spectralPeterssonHilbertProfile k G))
  rw [gamma0PeterssonInner_eq_hilbert N k F G hF hG] at h
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow,gamma0PeterssonHilbert_norm_sq_integral N k F hF,
    gamma0PeterssonHilbert_norm_sq_integral N k G hG] at hs
  exact hs

end ArtinMatthews
