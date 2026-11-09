module

public import ArtinMatthews.SpectralJForwardReality


set_option backward.privateInPublic true
@[expose] public section

/-! Algebraic realness of the exact spectral weight on the two axes.
This makes no holomorphy claim at its nonreal cosh zeros. -/
noncomputable section
open Set Complex
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralJForwardSpectralWeight_even (f : ℝ → ℂ) :
    Function.Even (spectralJForwardSpectralWeight f) := by
  intro z
  change spectralJForwardSpectralWeight f (-z) = spectralJForwardSpectralWeight f z
  rw [spectralJForwardSpectralWeight,spectralJForwardSpectralWeight,mul_neg,Complex.cosh_neg,
    spectralJForwardTransform_even f]

theorem spectralJForwardSpectralWeight_conj (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (z : ℂ) :
    conj (spectralJForwardSpectralWeight f z) = spectralJForwardSpectralWeight f (conj z) := by
  rw [spectralJForwardSpectralWeight,spectralJForwardSpectralWeight,map_mul,map_div₀,
    Complex.conj_ofReal,← Complex.cosh_conj,map_mul,Complex.conj_ofReal,
    spectralJForwardTransform_conj f hf hc hp hReal z]

theorem spectralJForwardSpectralWeight_real_im_eq_zero (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (t : ℝ) :
    (spectralJForwardSpectralWeight f (t : ℂ)).im = 0 := by
  have h := congrArg Complex.im (spectralJForwardSpectralWeight_conj f hf hc hp hReal (t : ℂ))
  simp only [Complex.conj_im,Complex.conj_ofReal] at h
  linarith

theorem spectralJForwardSpectralWeight_imaginary_im_eq_zero (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (κ : ℝ) :
    (spectralJForwardSpectralWeight f ((κ : ℂ)*I)).im = 0 := by
  have h := spectralJForwardSpectralWeight_conj f hf hc hp hReal ((κ : ℂ)*I)
  rw [map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,
    spectralJForwardSpectralWeight_even f] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

end ArtinMatthews
