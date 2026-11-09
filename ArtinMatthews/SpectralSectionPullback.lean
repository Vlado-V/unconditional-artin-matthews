module

public import ArtinMatthews.SpectralSectionEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Actual smooth scalar sections and energy under Möbius pullback. -/

noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem spectralSection_smooth_pullback (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) :
    ContDiffOn ℝ ∞ (fun w : ℂ => F (g • UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im} := by
  let m : ℂ → ℂ := fun w => UpperHalfPlane.num g w / UpperHalfPlane.denom g w
  have he {w : ℂ} (hw : 0 < w.im) :
      m w = ((g • (⟨w,hw⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) :=
    (UpperHalfPlane.coe_smul_of_det_pos hg (⟨w,hw⟩ : UpperHalfPlane)).symm
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  intro w hw
  have hm : ContDiffAt ℝ ∞ m w := by
    have hden : UpperHalfPlane.denom g w ≠ 0 := UpperHalfPlane.denom_ne_zero g ⟨w,hw⟩
    have hmc : ContDiffAt ℂ ∞ m w := by
      dsimp only [m,UpperHalfPlane.num,UpperHalfPlane.denom]
      fun_prop (disch := exact hden)
    exact hmc.restrict_scalars ℝ
  have hpositive : 0 < (m w).im := by rw [he hw]; exact (g • (⟨w,hw⟩ : UpperHalfPlane)).im_pos
  have hcomp := (hF.contDiffAt (hopen.mem_nhds hpositive)).comp w hm
  apply (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hopen.mem_nhds hw] with v hv
  change F (g • UpperHalfPlane.ofComplex v) = F (UpperHalfPlane.ofComplex (m v))
  rw [he hv,UpperHalfPlane.ofComplex_apply,UpperHalfPlane.ofComplex_apply_of_im_pos hv]

theorem h2SectionEnergy_pullback (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    (z : UpperHalfPlane) :
    h2SectionEnergy (fun v => F (g • v)) z = h2SectionEnergy F (g • z) := by
  have hf : DifferentiableAt ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      ((g • z : UpperHalfPlane) : ℂ) :=
    (hF.contDiffAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (g • z).im_pos)).differentiableAt (by simp)
  simpa only [h2SectionEnergy,UpperHalfPlane.ofComplex_apply] using
    h2FunctionEnergy_mobius (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) g hg z hf

end ArtinMatthews
