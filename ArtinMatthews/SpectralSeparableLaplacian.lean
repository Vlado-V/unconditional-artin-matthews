module

public import ArtinMatthews.SpectralSectionLaplacian
public import ArtinMatthews.SpectralRellichCoordinates
public import Mathlib.Analysis.Calculus.ContDiff.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! The exact positive hyperbolic Laplacian of a separable complex test.
Both derivatives are the actual one-dimensional `deriv`; no formal symbol
or assumed differential identity enters the constant-term reduction. -/

noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews

theorem spectralPlane_fderiv_separable_x (χ η : ℝ → ℂ)
    (hχ : Differentiable ℝ χ) (hη : Differentiable ℝ η) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => χ q.1 * η q.2) p (1,0) = deriv χ p.1 * η p.2 := by
  have hF : DifferentiableAt ℝ (fun q : ℝ × ℝ => χ q.1 * η q.2) p :=
    ((hχ p.1).comp p differentiableAt_fst).mul ((hη p.2).comp p differentiableAt_snd)
  rw [← spectralPlanePartialX_eq_fderiv hF]
  exact deriv_mul_const (hχ p.1) (η p.2)

theorem spectralPlane_fderiv_separable_y (χ η : ℝ → ℂ)
    (hχ : Differentiable ℝ χ) (hη : Differentiable ℝ η) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => χ q.1 * η q.2) p (0,1) = χ p.1 * deriv η p.2 := by
  have hF : DifferentiableAt ℝ (fun q : ℝ × ℝ => χ q.1 * η q.2) p :=
    ((hχ p.1).comp p differentiableAt_fst).mul ((hη p.2).comp p differentiableAt_snd)
  rw [← spectralPlanePartialY_eq_fderiv hF]
  exact deriv_const_mul (χ p.1) (hη p.2)

theorem spectralPlaneSecond_separable_zero (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) (p : ℝ × ℝ) :
    spectralPlaneSecond (fun q : ℝ × ℝ => χ q.1 * η q.2) 0 p = deriv (deriv χ) p.1 * η p.2 := by
  have hdχ := (contDiff_infty_iff_deriv.mp hχ).2
  unfold spectralPlaneSecond
  simp only [spectralPlaneDirection,Matrix.cons_val_zero]
  simp_rw [spectralPlane_fderiv_separable_x χ η (hχ.differentiable (by simp)) (hη.differentiable (by simp))]
  exact spectralPlane_fderiv_separable_x (deriv χ) η (hdχ.differentiable (by simp))
    (hη.differentiable (by simp)) p

theorem spectralPlaneSecond_separable_one (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) (p : ℝ × ℝ) :
    spectralPlaneSecond (fun q : ℝ × ℝ => χ q.1 * η q.2) 1 p = χ p.1 * deriv (deriv η) p.2 := by
  have hdη := (contDiff_infty_iff_deriv.mp hη).2
  unfold spectralPlaneSecond
  simp only [spectralPlaneDirection,Matrix.cons_val_one,Matrix.cons_val_zero]
  simp_rw [spectralPlane_fderiv_separable_y χ η (hχ.differentiable (by simp)) (hη.differentiable (by simp))]
  exact spectralPlane_fderiv_separable_y χ (deriv η) (hχ.differentiable (by simp))
    (hdη.differentiable (by simp)) p

theorem spectralPlanePositiveHyperbolic_separable (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) (p : ℝ × ℝ) :
    spectralPlanePositiveHyperbolic (fun q : ℝ × ℝ => χ q.1 * η q.2) p =
      -(p.2^2) • (deriv (deriv χ) p.1 * η p.2 + χ p.1 * deriv (deriv η) p.2) := by
  simp only [spectralPlanePositiveHyperbolic,spectralPlanePositiveSecond,Fin.sum_univ_two,
    spectralPlaneSecond_separable_zero χ η hχ hη,spectralPlaneSecond_separable_one χ η hχ hη,
    neg_smul,smul_neg]

theorem h2SectionPositiveLaplacian_separable (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (fun w : UpperHalfPlane => χ w.re * η w.im) z =
      -(z.im^2) • (deriv (deriv χ) z.re * η z.im + χ z.re * deriv (deriv η) z.im) := by
  rw [h2SectionPositiveLaplacian_representation _ (fun p : ℝ × ℝ => χ p.1 * η p.2)
    (fun _ => rfl)]
  exact spectralPlanePositiveHyperbolic_separable χ η hχ hη (z.re,z.im)

end ArtinMatthews
