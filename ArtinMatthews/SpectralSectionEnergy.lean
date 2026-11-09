module

public import ArtinMatthews.SpectralHyperbolicEnergyTransport
public import Mathlib.Analysis.Calculus.ContDiff.Operations


set_option backward.privateInPublic true
@[expose] public section

/-! Actual invariant energy density of smooth scalar automorphic sections. -/

noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

/-- The actual hyperbolically scaled derivative energy of a scalar section. -/
def h2SectionEnergy (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℝ :=
  z.im ^ 2 * h2FunctionEnergy (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) z

theorem h2SectionEnergy_nonneg (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    0 ≤ h2SectionEnergy F z :=
  mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Smoothness gives continuity of the actual differential energy. -/
theorem h2SectionEnergy_continuous (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) : Continuous (h2SectionEnergy F) := by
  have hd : Continuous (fun z : UpperHalfPlane =>
      fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (z : ℂ)) :=
    (hF.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const Complex.continuous_im) (by simp)).comp_continuous
      UpperHalfPlane.continuous_coe (fun z => z.im_pos)
  exact (UpperHalfPlane.continuous_im.pow 2).mul
    (((hd.clm_apply continuous_const).norm.pow 2).add
      ((hd.clm_apply continuous_const).norm.pow 2))

/-- Invariance is derived from the actual Möbius derivative, not attached as
extra data to the energy. -/
theorem h2SectionEnergy_invariant (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    (hinv : ∀ z : UpperHalfPlane, F (g • z) = F z) (z : UpperHalfPlane) :
    h2SectionEnergy F (g • z) = h2SectionEnergy F z := by
  let f : ℂ → ℂ := fun w => F (UpperHalfPlane.ofComplex w)
  have hf : DifferentiableAt ℝ f ((g • z : UpperHalfPlane) : ℂ) :=
    (hF.contDiffAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (g • z).im_pos)).differentiableAt (by simp)
  have h := h2FunctionEnergy_mobius f g hg z hf
  have he : (fun w : ℂ => f (g • UpperHalfPlane.ofComplex w : UpperHalfPlane)) = f := by
    funext w
    simp only [f, UpperHalfPlane.ofComplex_apply]
    exact hinv _
  rw [he] at h
  exact h.symm

/-- Energy vanishes off the actual topological support of the section. -/
theorem h2SectionEnergy_eq_zero_of_notMem_tsupport (F : UpperHalfPlane → ℂ)
    {z : UpperHalfPlane} (hz : z ∉ tsupport F) : h2SectionEnergy F z = 0 := by
  have hc : ContinuousAt UpperHalfPlane.ofComplex (z : ℂ) :=
    (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hc' : Tendsto UpperHalfPlane.ofComplex (𝓝 (z : ℂ)) (𝓝 z) := by
    simpa only [ContinuousAt, UpperHalfPlane.ofComplex_apply] using hc
  have he : (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) =ᶠ[𝓝 (z : ℂ)]
      (fun _ => (0 : ℂ)) := by
    have h := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto hc'
    simpa only [Function.comp_def, Pi.zero_apply] using h
  unfold h2SectionEnergy h2FunctionEnergy h2TangentEnergy
  rw [he.fderiv_eq]
  simp

end ArtinMatthews
