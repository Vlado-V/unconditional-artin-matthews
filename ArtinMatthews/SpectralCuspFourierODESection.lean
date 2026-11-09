module

public import ArtinMatthews.SpectralCuspFourierODEHorizontal
public import ArtinMatthews.SpectralSectionLaplacian


set_option backward.privateInPublic true
@[expose] public section

/-! Actual vertical differentiation of a section's literal Fourier
coefficient on the positive half-line. A globally smooth extension is used
only locally, with actual germs transferring its first and second fields. -/
namespace ArtinMatthews
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

 def cuspSectionFourierCoeff (w : ℝ) (n : ℤ) (F : UpperHalfPlane → ℂ) : ℝ → ℂ :=
  cuspHorizontalWeightedMean w (cuspFourierPhase w n) (spectralSectionPlane F)

 def cuspSectionFourierCoeffVertical (w : ℝ) (n : ℤ) (F : UpperHalfPlane → ℂ) : ℝ → ℂ :=
  cuspHorizontalWeightedMean w (cuspFourierPhase w n)
    (fun p => fderiv ℝ (spectralSectionPlane F) p (0, 1))

 def cuspSectionFourierCoeffSecond (w : ℝ) (n : ℤ) (F : UpperHalfPlane → ℂ) : ℝ → ℂ :=
  cuspHorizontalWeightedMean w (cuspFourierPhase w n) (spectralPlaneSecond (spectralSectionPlane F) 1)

 theorem cuspHorizontalWeightedMean_congr_slice (w : ℝ) (χ : ℝ → ℂ)
    {G H : ℝ × ℝ → ℂ} {y : ℝ} (he : ∀ x, G (x, y) = H (x, y)) :
    cuspHorizontalWeightedMean w χ G y = cuspHorizontalWeightedMean w χ H y := by
  unfold cuspHorizontalWeightedMean cuspHorizontalMean
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => congrArg (fun v : ℂ => χ x * v) (he x)

 theorem spectralSectionSmoothExtension_germ {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ) {p : ℝ × ℝ} (hp : Y < p.2) :
    spectralSectionSmoothExtension Y F =ᶠ[𝓝 p] spectralSectionPlane F := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
  exact spectralSectionSmoothExtension_eq hY F hq.le

 theorem spectralPlaneSecond_vertical_eq (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    spectralPlaneSecond G 1 p = fderiv ℝ (fun q => fderiv ℝ G q (0, 1)) p (0, 1) := rfl

 theorem cuspSectionFourierCoeff_hasDerivAt (w : ℝ) (n : ℤ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cuspSectionFourierCoeff w n F) (cuspSectionFourierCoeffVertical w n F y) y := by
  let Y := y / 2
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYy : Y < y := by dsimp [Y]; linarith
  let G := spectralSectionSmoothExtension Y F
  have hG : ContDiff ℝ ∞ G := spectralSectionSmoothExtension_contDiff hY F hF
  have hd := cuspHorizontalWeightedMean_hasDerivAt w (cuspFourierPhase_contDiff w n) hG hy
  have hv : cuspHorizontalWeightedMean w (cuspFourierPhase w n)
      (fun p => fderiv ℝ G p (0, 1)) y = cuspSectionFourierCoeffVertical w n F y := by
    apply cuspHorizontalWeightedMean_congr_slice
    intro x
    exact congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℂ => A (0, 1))
      (spectralSectionSmoothExtension_germ hY F (p := (x, y)) hYy).fderiv_eq
  rw [hv] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hYy] with t ht
  change cuspHorizontalWeightedMean w (cuspFourierPhase w n) (spectralSectionPlane F) t = _
  apply cuspHorizontalWeightedMean_congr_slice
  intro x
  exact (spectralSectionSmoothExtension_eq hY F (p := (x, t)) ht.le).symm

 theorem cuspSectionFourierCoeff_deriv (w : ℝ) (n : ℤ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    deriv (cuspSectionFourierCoeff w n F) y = cuspSectionFourierCoeffVertical w n F y :=
  (cuspSectionFourierCoeff_hasDerivAt w n F hF hy).deriv

 theorem cuspSectionFourierCoeffVertical_hasDerivAt (w : ℝ) (n : ℤ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (cuspSectionFourierCoeffVertical w n F) (cuspSectionFourierCoeffSecond w n F y) y := by
  let Y := y / 2
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYy : Y < y := by dsimp [Y]; linarith
  let G := spectralSectionSmoothExtension Y F
  have hG : ContDiff ℝ ∞ G := spectralSectionSmoothExtension_contDiff hY F hF
  have hD : ContDiff ℝ ∞ (fun p => fderiv ℝ G p (0, 1)) :=
    (hG.fderiv_right (by simp)).clm_apply contDiff_const
  have hd := cuspHorizontalWeightedMean_hasDerivAt w (cuspFourierPhase_contDiff w n) hD hy
  have hv : cuspHorizontalWeightedMean w (cuspFourierPhase w n)
      (fun p => fderiv ℝ (fun q => fderiv ℝ G q (0, 1)) p (0, 1)) y =
        cuspSectionFourierCoeffSecond w n F y := by
    apply cuspHorizontalWeightedMean_congr_slice
    intro x
    rw [← spectralPlaneSecond_vertical_eq]
    exact spectralPlaneSecond_congr_of_eventuallyEq G (spectralSectionPlane F)
      (spectralSectionSmoothExtension_germ hY F (p := (x, y)) hYy) 1
  rw [hv] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hYy] with t ht
  change cuspHorizontalWeightedMean w (cuspFourierPhase w n)
    (fun p => fderiv ℝ (spectralSectionPlane F) p (0, 1)) t = _
  apply cuspHorizontalWeightedMean_congr_slice
  intro x
  exact congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℂ => A (0, 1))
    (spectralSectionSmoothExtension_germ hY F (p := (x, t)) ht).fderiv_eq.symm

 theorem cuspSectionFourierCoeff_deriv_hasDerivAt (w : ℝ) (n : ℤ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (cuspSectionFourierCoeff w n F)) (cuspSectionFourierCoeffSecond w n F y) y := by
  apply (cuspSectionFourierCoeffVertical_hasDerivAt w n F hF hy).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact cuspSectionFourierCoeff_deriv w n F hF ht

 theorem cuspSectionFourierCoeff_second_deriv (w : ℝ) (n : ℤ) (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (cuspSectionFourierCoeff w n F)) y = cuspSectionFourierCoeffSecond w n F y :=
  (cuspSectionFourierCoeff_deriv_hasDerivAt w n F hF hy).deriv

end
end ArtinMatthews
