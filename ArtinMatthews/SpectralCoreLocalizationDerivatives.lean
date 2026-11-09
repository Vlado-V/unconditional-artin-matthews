module

public import ArtinMatthews.SpectralCoreLocalization


set_option backward.privateInPublic true
@[expose] public section

/-! Exact Cartesian derivatives of the actual hyperbolic section and its
compact cutoff. -/

namespace ArtinMatthews
noncomputable section

open Set
open scoped ContDiff

theorem spectralPlanePartialX_mul {f g : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    spectralPlanePartialX (fun q => f q*g q) p =
      spectralPlanePartialX f p*g p+f p*spectralPlanePartialX g p := by
  have hd : HasDerivAt (fun t : ℝ => (t,p.2)) (1,0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hf' := (hf.hasFDerivAt.comp_hasDerivAt p.1 hd).differentiableAt
  have hg' := (hg.hasFDerivAt.comp_hasDerivAt p.1 hd).differentiableAt
  exact (hf'.hasDerivAt.mul hg'.hasDerivAt).deriv

theorem spectralPlanePartialY_mul {f g : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    spectralPlanePartialY (fun q => f q*g q) p =
      spectralPlanePartialY f p*g p+f p*spectralPlanePartialY g p := by
  have hd : HasDerivAt (fun t : ℝ => (p.1,t)) (0,1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hf' := (hf.hasFDerivAt.comp_hasDerivAt p.2 hd).differentiableAt
  have hg' := (hg.hasFDerivAt.comp_hasDerivAt p.2 hd).differentiableAt
  exact (hf'.hasDerivAt.mul hg'.hasDerivAt).deriv

theorem spectralSectionPlane_coordinate_derivatives (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) {p : ℝ × ℝ} (hp : 0 < p.2) :
    spectralPlanePartialX (spectralSectionPlane F) p =
      fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (Complex.equivRealProdCLM.symm p) 1 ∧
    spectralPlanePartialY (spectralSectionPlane F) p =
      fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (Complex.equivRealProdCLM.symm p) Complex.I := by
  have hpos : 0 < (Complex.equivRealProdCLM.symm p).im := by
    simpa [Complex.equivRealProdCLM_symm_apply] using hp
  have hf : DifferentiableAt ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      (Complex.equivRealProdCLM.symm p) :=
    (hF.contDiffAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos)).differentiableAt (by simp)
  have hpF : DifferentiableAt ℝ (spectralSectionPlane F) p :=
    (spectralSectionPlane_contDiffAt F hF hp).differentiableAt (by simp)
  have he : fderiv ℝ (spectralSectionPlane F) p =
      (fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (Complex.equivRealProdCLM.symm p)).comp
        Complex.equivRealProdCLM.symm.toContinuousLinearMap := by
    change fderiv ℝ ((fun w : ℂ => F (UpperHalfPlane.ofComplex w)) ∘
      Complex.equivRealProdCLM.symm) p = _
    rw [fderiv_comp p hf Complex.equivRealProdCLM.symm.differentiableAt,
      Complex.equivRealProdCLM.symm.fderiv]
  constructor
  · rw [spectralPlanePartialX_eq_fderiv hpF, he, ContinuousLinearMap.comp_apply]
    congr 1
  · rw [spectralPlanePartialY_eq_fderiv hpF, he, ContinuousLinearMap.comp_apply]
    congr 1

theorem spectralSectionPlane_energy (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) {p : ℝ × ℝ} (hp : 0 < p.2) :
    h2SectionEnergy F (UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p)) =
      p.2^2*(‖spectralPlanePartialX (spectralSectionPlane F) p‖^2+
        ‖spectralPlanePartialY (spectralSectionPlane F) p‖^2) := by
  have hpos : 0 < (Complex.equivRealProdCLM.symm p).im := by
    simpa [Complex.equivRealProdCLM_symm_apply] using hp
  obtain ⟨hx,hy⟩ := spectralSectionPlane_coordinate_derivatives F hF hp
  rw [hx,hy]
  simp only [h2SectionEnergy, h2FunctionEnergy, h2TangentEnergy,
    UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
  congr 1

end
end ArtinMatthews
