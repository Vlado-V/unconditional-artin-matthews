module

public import ArtinMatthews.SpectralRealSeparableLaplacian
public import ArtinMatthews.SpectralSectionGradientRepresentation


set_option backward.privateInPublic true
@[expose] public section

/-! Exact frame derivatives of the actual separable compact tests used to
identify weak horizontal means and their genuine vertical derivative. -/

noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews

theorem h2SeparableSmoothSeed_gradient_zero (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionGradient (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z 0 =
      z.im • (deriv χ z.re * η z.im) := by
  rw [h2SectionGradient_representation
    (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val (fun p : ℝ × ℝ => χ p.1 * η p.2)
    ((hχ.comp contDiff_fst).mul (hη.comp contDiff_snd)) (fun _ => rfl)]
  change z.im • fderiv ℝ (fun p : ℝ × ℝ => χ p.1 * η p.2) (z.re,z.im) (1,0) = _
  rw [spectralPlane_fderiv_separable_x χ η (hχ.differentiable (by simp)) (hη.differentiable (by simp))]

theorem h2SeparableSmoothSeed_gradient_one (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionGradient (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z 1 =
      z.im • (χ z.re * deriv η z.im) := by
  rw [h2SectionGradient_representation
    (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val (fun p : ℝ × ℝ => χ p.1 * η p.2)
    ((hχ.comp contDiff_fst).mul (hη.comp contDiff_snd)) (fun _ => rfl)]
  change z.im • fderiv ℝ (fun p : ℝ × ℝ => χ p.1 * η p.2) (z.re,z.im) (0,1) = _
  rw [spectralPlane_fderiv_separable_y χ η (hχ.differentiable (by simp)) (hη.differentiable (by simp))]

theorem h2RealSeparableSmoothSeed_gradient_zero (χ η : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionGradient (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z 0 =
      ((z.im * (deriv χ z.re * η z.im) : ℝ) : ℂ) := by
  have hχc : ContDiff ℝ ∞ (fun x => (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hηc : ContDiff ℝ ∞ (fun y => (η y : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  rw [h2SectionGradient_representation
    (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val
    (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ))
    ((hχc.comp contDiff_fst).mul (hηc.comp contDiff_snd)) (fun _ => rfl)]
  change z.im • fderiv ℝ (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ)) (z.re,z.im) (1,0) = _
  rw [spectralPlane_fderiv_separable_x (fun x => (χ x : ℂ)) (fun y => (η y : ℂ))
    (hχc.differentiable (by simp)) (hηc.differentiable (by simp))]
  simp only [spectral_deriv_ofReal χ (hχ.differentiable (by simp)),
    Complex.real_smul,Complex.ofReal_mul]

theorem h2RealSeparableSmoothSeed_gradient_one (χ η : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionGradient (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z 1 =
      ((z.im * (χ z.re * deriv η z.im) : ℝ) : ℂ) := by
  have hχc : ContDiff ℝ ∞ (fun x => (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hηc : ContDiff ℝ ∞ (fun y => (η y : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  rw [h2SectionGradient_representation
    (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val
    (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ))
    ((hχc.comp contDiff_fst).mul (hηc.comp contDiff_snd)) (fun _ => rfl)]
  change z.im • fderiv ℝ (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ)) (z.re,z.im) (0,1) = _
  rw [spectralPlane_fderiv_separable_y (fun x => (χ x : ℂ)) (fun y => (η y : ℂ))
    (hχc.differentiable (by simp)) (hηc.differentiable (by simp))]
  simp only [spectral_deriv_ofReal η (hη.differentiable (by simp)),
    Complex.real_smul,Complex.ofReal_mul]

end ArtinMatthews
