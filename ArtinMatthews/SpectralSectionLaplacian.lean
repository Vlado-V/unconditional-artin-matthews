module

public import ArtinMatthews.SpectralHyperbolicComplexGreen
public import ArtinMatthews.SpectralSmoothSeedPlaneExtension


set_option backward.privateInPublic true
@[expose] public section

/-! The literal positive H² differential Laplacian of a scalar section,
independent of any choice of smooth plane extension. -/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff MatrixGroups

namespace ArtinMatthews

def h2SectionPositiveLaplacian (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  spectralPlanePositiveHyperbolic (spectralSectionPlane F) (z.re,z.im)

theorem spectralPlaneSecond_congr_of_eventuallyEq (f g : ℝ × ℝ → ℂ)
    {p : ℝ × ℝ} (h : f =ᶠ[𝓝 p] g) (i : Fin 2) :
    spectralPlaneSecond f i p = spectralPlaneSecond g i p := by
  have hd : (fun q => fderiv ℝ f q (spectralPlaneDirection i)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (spectralPlaneDirection i)) :=
    h.fderiv.mono (fun q hq => congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℂ => A (spectralPlaneDirection i)) hq)
  exact congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℂ => A (spectralPlaneDirection i)) hd.fderiv_eq

theorem spectralPlanePositiveHyperbolic_congr_of_eventuallyEq (f g : ℝ × ℝ → ℂ)
    {p : ℝ × ℝ} (h : f =ᶠ[𝓝 p] g) :
    spectralPlanePositiveHyperbolic f p = spectralPlanePositiveHyperbolic g p := by
  unfold spectralPlanePositiveHyperbolic spectralPlanePositiveSecond
  congr 2
  exact Finset.sum_congr rfl (fun i _ => spectralPlaneSecond_congr_of_eventuallyEq f g h i)

theorem spectralSectionPlane_representation_germ (F : UpperHalfPlane → ℂ)
    (φ : ℝ × ℝ → ℂ) (he : ∀ z : UpperHalfPlane, φ (z.re,z.im) = F z)
    (z : UpperHalfPlane) : spectralSectionPlane F =ᶠ[𝓝 (z.re,z.im)] φ := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos] with p hp
  let w := UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p)
  have him : 0 < (Complex.equivRealProdCLM.symm p).im := by
    simpa [Complex.equivRealProdCLM_symm_apply] using hp
  have hc : (w.re,w.im) = p := by
    dsimp only [w]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    exact Complex.equivRealProdCLM.apply_symm_apply p
  rw [← hc,spectralSectionPlane_at_upper,he]

theorem h2SectionPositiveLaplacian_representation (F : UpperHalfPlane → ℂ)
    (φ : ℝ × ℝ → ℂ) (he : ∀ z : UpperHalfPlane, φ (z.re,z.im) = F z)
    (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian F z = spectralPlanePositiveHyperbolic φ (z.re,z.im) :=
  spectralPlanePositiveHyperbolic_congr_of_eventuallyEq _ _
    (spectralSectionPlane_representation_germ F φ he z)

end ArtinMatthews
