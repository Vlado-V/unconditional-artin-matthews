module

public import ArtinMatthews.SpectralJForwardRealWeight


set_option backward.privateInPublic true
@[expose] public section

/-! Exact complex linearity in the original compact positive test. -/
noncomputable section
open Set MeasureTheory Complex

namespace ArtinMatthews

theorem spectralJForwardTransform_const_mul (a : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    spectralJForwardTransform (fun x => a*f x) z = a*spectralJForwardTransform f z := by
  unfold spectralJForwardTransform
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change a*f x*spectralJForwardKernel z x/(x : ℂ) =
    a*(f x*spectralJForwardKernel z x/(x : ℂ))
  ring

theorem spectralJForwardTransform_add (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) (z : ℂ) :
    spectralJForwardTransform (f+g) z = spectralJForwardTransform f z + spectralJForwardTransform g z := by
  have hA : spectralBesselJOrderTransform (f+g) = spectralBesselJOrderTransform f + spectralBesselJOrderTransform g := by
    funext ν
    unfold spectralBesselJOrderTransform
    change (∫ x in Ioi (0 : ℝ), (f x+g x)*Complex.besselJ ν (x : ℂ)/(x : ℂ)) =
      (∫ x in Ioi (0 : ℝ), f x*Complex.besselJ ν (x : ℂ)/(x : ℂ)) +
        (∫ x in Ioi (0 : ℝ), g x*Complex.besselJ ν (x : ℂ)/(x : ℂ))
    rw [← integral_add (spectralBesselJOrderTransform_integrable f hf hfc hfp ν)
      (spectralBesselJOrderTransform_integrable g hg hgc hgp ν)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change (f x+g x)*Complex.besselJ ν (x : ℂ)/(x : ℂ) =
      f x*Complex.besselJ ν (x : ℂ)/(x : ℂ) + g x*Complex.besselJ ν (x : ℂ)/(x : ℂ)
    ring
  have hfgp : tsupport (f+g) ⊆ Ioi (0 : ℝ) := (tsupport_add f g).trans (union_subset hfp hgp)
  rw [spectralJForwardTransform_eq_divided_order (f+g) (hf.add hg) (hfc.add hgc) hfgp z,
    spectralJForwardTransform_eq_divided_order f hf hfc hfp z,
    spectralJForwardTransform_eq_divided_order g hg hgc hgp z,hA]
  by_cases hz : z = 0
  · subst z
    simp only [ite_true]
    rw [deriv_add (spectralBesselJOrderTransform_differentiable f hf hfc hfp 0)
      (spectralBesselJOrderTransform_differentiable g hg hgc hgp 0)]
    ring
  · simp only [ite_eq_right hz, Pi.add_apply]
    ring

theorem spectralJForwardSpectralWeight_const_mul (a : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    spectralJForwardSpectralWeight (fun x => a*f x) z = a*spectralJForwardSpectralWeight f z := by
  rw [spectralJForwardSpectralWeight,spectralJForwardSpectralWeight,
    spectralJForwardTransform_const_mul]
  ring

theorem spectralJForwardSpectralWeight_add (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfp : tsupport f ⊆ Ioi (0 : ℝ)) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) (z : ℂ) :
    spectralJForwardSpectralWeight (f+g) z = spectralJForwardSpectralWeight f z + spectralJForwardSpectralWeight g z := by
  rw [spectralJForwardSpectralWeight,spectralJForwardSpectralWeight,spectralJForwardSpectralWeight,
    spectralJForwardTransform_add f g hf hg hfc hgc hfp hgp]
  ring

end ArtinMatthews
