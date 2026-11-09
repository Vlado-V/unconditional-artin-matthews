module

public import ArtinMatthews.SpectralSectionGradient
public import ArtinMatthews.SpectralSectionPullback


set_option backward.privateInPublic true
@[expose] public section

/-! Actual complex Dirichlet pairings are invariant under the genuine
positive-determinant Möbius pullback. This is derived by polarization from
the proved differential-energy transformation, not assumed as covariance. -/

noncomputable section
open Set
open scoped ContDiff MatrixGroups InnerProductSpace

namespace ArtinMatthews

theorem h2SectionGradient_inner_re (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (hG : ContDiffOn ℝ ∞ (fun w : ℂ => G (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (z : UpperHalfPlane) :
    (inner ℂ (h2SectionGradient F z) (h2SectionGradient G z)).re =
      (h2SectionEnergy (F+G) z-h2SectionEnergy F z-h2SectionEnergy G z)/2 := by
  rw [← h2SectionGradient_norm_sq (F+G),h2SectionGradient_add F G hF hG,
    ← h2SectionGradient_norm_sq F,← h2SectionGradient_norm_sq G]
  simpa only [pow_two,RCLike.re_eq_complex_re] using
    (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
      (𝕜 := ℂ) (h2SectionGradient F z) (h2SectionGradient G z))

theorem h2SectionGradient_inner_re_pullback (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (hG : ContDiffOn ℝ ∞ (fun w : ℂ => G (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (z : UpperHalfPlane) :
    (inner ℂ (h2SectionGradient (fun v => F (g • v)) z)
      (h2SectionGradient (fun v => G (g • v)) z)).re =
      (inner ℂ (h2SectionGradient F (g • z)) (h2SectionGradient G (g • z))).re := by
  rw [h2SectionGradient_inner_re _ _ (spectralSection_smooth_pullback F hF g hg)
      (spectralSection_smooth_pullback G hG g hg),h2SectionGradient_inner_re F G hF hG]
  change (h2SectionEnergy (fun v => (F+G) (g • v)) z-
    h2SectionEnergy (fun v => F (g • v)) z-h2SectionEnergy (fun v => G (g • v)) z)/2 = _
  rw [h2SectionEnergy_pullback (F+G) (hF.add hG) g hg,
    h2SectionEnergy_pullback F hF g hg,h2SectionEnergy_pullback G hG g hg]

/-- Full complex sesquilinear covariance of the actual H² frame gradient. -/
theorem h2SectionGradient_inner_pullback (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (hG : ContDiffOn ℝ ∞ (fun w : ℂ => G (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (z : UpperHalfPlane) :
    inner ℂ (h2SectionGradient (fun v => F (g • v)) z)
      (h2SectionGradient (fun v => G (g • v)) z) =
      inner ℂ (h2SectionGradient F (g • z)) (h2SectionGradient G (g • z)) := by
  apply Complex.ext
  · exact h2SectionGradient_inner_re_pullback F G hF hG g hg z
  · have hIG : ContDiffOn ℝ ∞ (fun w : ℂ => (Complex.I • G) (UpperHalfPlane.ofComplex w))
        {w : ℂ | 0 < w.im} := hG.const_smul Complex.I
    have hi := h2SectionGradient_inner_re_pullback F (Complex.I • G) hF hIG g hg z
    change (inner ℂ (h2SectionGradient (fun v => F (g • v)) z)
      (h2SectionGradient (Complex.I • (fun v => G (g • v))) z)).re = _ at hi
    rw [h2SectionGradient_smul Complex.I _ (spectralSection_smooth_pullback G hG g hg),
      h2SectionGradient_smul Complex.I G hG] at hi
    simp only [inner_smul_right,Complex.mul_re,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,zero_sub] at hi
    exact neg_injective hi

end ArtinMatthews
