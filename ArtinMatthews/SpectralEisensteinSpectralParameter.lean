module

public import ArtinMatthews.SpectralGamma0AmbientResolvent


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Eisenstein eigenvalue lies in the proved ambient resolvent
region throughout its convergent half-plane. -/
noncomputable section
namespace ArtinMatthews

theorem eisensteinSpectralParameter_off_nonnegative_ray (s : ℂ) (hs : 1 < s.re) :
    (s*(1-s)).re < ‖s*(1-s)‖ := by
  have hre := Complex.re_le_norm (s*(1-s))
  have hn := norm_nonneg (s*(1-s))
  have hsq := Complex.sq_norm (s*(1-s))
  rw [Complex.normSq_apply] at hsq
  by_contra h
  have he : ‖s*(1-s)‖=(s*(1-s)).re := le_antisymm (not_lt.mp h) hre
  have hi : (s*(1-s)).im=0 := by nlinarith [sq_nonneg ((s*(1-s)).im)]
  have hsi : s.im=0 := by
    simp only [Complex.mul_im,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im] at hi
    nlinarith
  simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,hsi] at he
  nlinarith

end ArtinMatthews
