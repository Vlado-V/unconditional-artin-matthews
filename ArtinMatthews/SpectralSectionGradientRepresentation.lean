module

public import ArtinMatthews.SpectralSectionLaplacianTests
public import ArtinMatthews.SpectralSectionGradient


set_option backward.privateInPublic true
@[expose] public section

/-! The actual frame gradient of a hyperbolic section agrees with the
coordinate derivatives of any genuine smooth plane representative. -/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace ArtinMatthews

theorem h2SectionGradient_representation (F : UpperHalfPlane → ℂ)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (he : ∀ z : UpperHalfPlane, φ (z.re,z.im) = F z)
    (z : UpperHalfPlane) (i : Fin 2) :
    h2SectionGradient F z i =
      z.im • fderiv ℝ φ (z.re,z.im) (spectralPlaneDirection i) := by
  have he' : (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) =ᶠ[𝓝 (z : ℂ)]
      (fun w : ℂ => φ (Complex.equivRealProdCLM w)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos] with w hw
    have hh := he (UpperHalfPlane.ofComplex w)
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      Complex.equivRealProdCLM_apply, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im] using hh.symm
  have hd : fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (z : ℂ) =
      (fderiv ℝ φ (z.re,z.im)).comp Complex.equivRealProdCLM.toContinuousLinearMap := by
    rw [he'.fderiv_eq]
    change fderiv ℝ (φ ∘ Complex.equivRealProdCLM) (z : ℂ) = _
    rw [fderiv_comp (z : ℂ) (hφ.differentiable (by simp) _) Complex.equivRealProdCLM.differentiableAt,
      Complex.equivRealProdCLM.fderiv]
    rfl
  fin_cases i <;> simp [h2SectionGradient,spectralPlaneDirection,hd,
    ContinuousLinearMap.comp_apply,Complex.equivRealProdCLM_apply]

end ArtinMatthews
