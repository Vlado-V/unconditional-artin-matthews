module

public import ArtinMatthews.SpectralSectionEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Actual orthonormal-frame gradient vectors for H² scalar sections. -/

noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews

/-- The two actual coordinate derivatives, scaled by height. -/
def h2SectionGradient (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![z.im • (fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) z) 1,
    z.im • (fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) z) Complex.I]

theorem h2SectionGradient_norm_sq (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖h2SectionGradient F z‖ ^ 2 = h2SectionEnergy F z := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [h2SectionGradient, WithLp.ofLp_toLp, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, h2SectionEnergy, h2FunctionEnergy, h2TangentEnergy]
  ring

theorem h2SectionGradient_continuous (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) : Continuous (h2SectionGradient F) := by
  have hd : Continuous (fun z : UpperHalfPlane =>
      fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (z : ℂ)) :=
    (hF.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const Complex.continuous_im) (by simp)).comp_continuous
      UpperHalfPlane.continuous_coe (fun z => z.im_pos)
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    exact UpperHalfPlane.continuous_im.smul (hd.clm_apply continuous_const)

private theorem h2_section_differentiable (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (z : UpperHalfPlane) :
    DifferentiableAt ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (z : ℂ) :=
  (hF.contDiffAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    z.im_pos)).differentiableAt (by simp)

theorem h2SectionGradient_add (F G : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (hG : ContDiffOn ℝ ∞ (fun w : ℂ => G (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (z : UpperHalfPlane) :
    h2SectionGradient (F + G) z = h2SectionGradient F z + h2SectionGradient G z := by
  have he : fderiv ℝ (fun w : ℂ => (F + G) (UpperHalfPlane.ofComplex w)) (z : ℂ) =
      fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (z : ℂ) +
      fderiv ℝ (fun w : ℂ => G (UpperHalfPlane.ofComplex w)) (z : ℂ) :=
    fderiv_add (h2_section_differentiable F hF z) (h2_section_differentiable G hG z)
  simp only [Pi.add_apply] at he
  ext i
  fin_cases i <;> simp [h2SectionGradient, he]

theorem h2SectionGradient_smul (c : ℂ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (z : UpperHalfPlane) :
    h2SectionGradient (c • F) z = c • h2SectionGradient F z := by
  have he : fderiv ℝ (fun w : ℂ => (c • F) (UpperHalfPlane.ofComplex w)) (z : ℂ) =
      c • fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (z : ℂ) :=
    fderiv_const_smul (h2_section_differentiable F hF z) c
  simp only [Pi.smul_apply, smul_eq_mul] at he
  ext i
  fin_cases i <;> simp [h2SectionGradient, he, mul_left_comm]

end ArtinMatthews
