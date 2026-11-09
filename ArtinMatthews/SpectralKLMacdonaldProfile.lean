module

public import ArtinMatthews.SpectralKLExpReciprocal
public import ArtinMatthews.SpectralMacdonaldReciprocal
public import ArtinMatthews.SpectralKLAnalysisIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The actual noncompact physical profile produced by Gaussian Weyl
integration, with its literal K analysis integral. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralKLMacdonaldProfile (x y : ℝ) : ℝ → ℂ :=
  spectralKLExpReciprocal ((x^2+y^2)/(2*x*y)) (x*y/2)

theorem spectralKLMacdonaldProfile_memLp {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    MemLp (spectralKLMacdonaldProfile x y) 2 spectralKLPhysicalMeasure := by
  apply spectralKLExpReciprocal_memLp
  · exact div_pos (by positivity) (by positivity)
  · positivity

theorem spectralKLMacdonaldProfile_kernel {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (t : ℝ) :
    schlafliBesselK ((t : ℂ)*Complex.I) z*spectralKLMacdonaldProfile x y z/(z : ℂ) =
      spectralMacdonaldReciprocalIntegrand x y t z := by
  unfold spectralKLMacdonaldProfile spectralKLExpReciprocal spectralMacdonaldReciprocalIntegrand
  rw [ite_eq_left hz]
  have he : -((((x^2+y^2)/(2*x*y) : ℝ) : ℂ))*(z : ℂ)-(((x*y/2 : ℝ) : ℂ))/(z : ℂ) =
      -(((x : ℂ)^2+(y : ℂ)^2)/(2*x*y))*(z : ℂ)-((x*y : ℝ) : ℂ)/(2*z) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hx.ne',Complex.ofReal_ne_zero.mpr hy.ne',
      Complex.ofReal_ne_zero.mpr hz.ne']
  rw [he]
  ring

theorem spectralKLMacdonaldProfile_kernel_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    IntegrableOn (fun z : ℝ => schlafliBesselK ((t : ℂ)*Complex.I) z*
      spectralKLMacdonaldProfile x y z/(z : ℂ)) (Ioi (0 : ℝ)) := by
  apply (spectralMacdonaldReciprocalIntegrand_integrable hx hy t).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact (spectralKLMacdonaldProfile_kernel hx hy hz t).symm

theorem spectralKLMacdonaldProfile_analysis_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    (∫ z in Ioi (0 : ℝ), schlafliBesselK ((t : ℂ)*Complex.I) z*
      spectralKLMacdonaldProfile x y z/(z : ℂ)) =
      2*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y := by
  calc
    _ = ∫ z in Ioi (0 : ℝ), spectralMacdonaldReciprocalIntegrand x y t z := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      exact spectralKLMacdonaldProfile_kernel hx hy hz t
    _ = _ := schlafliBesselK_imaginary_reciprocal_product hx hy t

end ArtinMatthews
