module

public import ArtinMatthews.SpectralKLMacdonaldPairing
public import ArtinMatthews.SpectralKLCompactInverse


set_option backward.privateInPublic true
@[expose] public section

/-! Literal compact physical-test pairing against the actual noncompact
Macdonald profile.  Reality is proved from the genuine kernels. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKLExpReciprocal_star (a b z : ℝ) :
    star (spectralKLExpReciprocal a b z) = spectralKLExpReciprocal a b z := by
  by_cases hz : 0 < z
  · rw [spectralKLExpReciprocal,ite_eq_left hz,
      show -(a : ℂ)*(z : ℂ)-(b : ℂ)/(z : ℂ) = ((-a*z-b/z : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp]
    exact Complex.conj_ofReal _
  · simp only [spectralKLExpReciprocal,ite_eq_right hz,star_zero]

theorem spectral_schlafli_imaginary_star (r : ℝ) {x : ℝ} (hx : 0 < x) :
    star (schlafliBesselK ((r : ℂ)*Complex.I) x) = schlafliBesselK ((r : ℂ)*Complex.I) x := by
  rw [schlafliBesselK_imaginary_eq_realKernel r hx]
  exact Complex.conj_ofReal _

theorem spectralKLMacdonaldPairing_compact {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (f : ℝ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ)) :
    (∫ z : ℝ, spectralKLMacdonaldProfile x y z*f z ∂spectralKLPhysicalMeasure) =
      ∫ r : ℝ, (2*schlafliBesselK ((r : ℂ)*Complex.I) x*
        schlafliBesselK ((r : ℂ)*Complex.I) y)*spectralKLPhysicalAnalysisIntegral f r
          ∂spectralKLSpectralMeasure := by
  let F := (spectralKLPhysical_compact_memLp f hf hfc hfp).toLp f
  let P := (spectralKLMacdonaldProfile_memLp hx hy).toLp (spectralKLMacdonaldProfile x y)
  calc
    _ = inner ℂ P F := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(spectralKLMacdonaldProfile_memLp hx hy).coeFn_toLp,
        (spectralKLPhysical_compact_memLp f hf hfc hfp).coeFn_toLp] with z hzP hzf
      rw [RCLike.inner_apply]
      change _ = F z*star (P z)
      rw [show F z = f z from hzf,show P z = spectralKLMacdonaldProfile x y z from hzP]
      rw [spectralKLMacdonaldProfile,spectralKLExpReciprocal_star]
      ring_nf
    _ = _ := by
      rw [spectralKLMacdonaldPairing hx hy F]
      apply integral_congr_ae
      filter_upwards [spectralKLAnalysis_compact_ae f hf hfc hfp] with r hr
      rw [show spectralKLAnalysis F r = spectralKLPhysicalAnalysisIntegral f r from hr,
        star_mul,star_mul,spectral_schlafli_imaginary_star r hx,
        spectral_schlafli_imaginary_star r hy]
      norm_num only [star_ofNat]
      ring_nf

end ArtinMatthews
