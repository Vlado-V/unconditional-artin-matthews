module

public import ArtinMatthews.SpectralMacdonaldProduct
public import ArtinMatthews.SpectralMultiplicativeInversion


set_option backward.privateInPublic true
@[expose] public section

/-! Reciprocal form of the genuine Macdonald product, with absolute
convergence. This is the kernel produced by Gaussian orbital integration. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralMacdonaldReciprocalIntegrand (x y t z : ℝ) : ℂ :=
  Complex.exp (-(((x : ℂ)^2+(y : ℂ)^2)/(2*x*y))*(z : ℂ)-((x*y : ℝ) : ℂ)/(2*z))*
    schlafliBesselK ((t : ℂ)*Complex.I) z/(z : ℂ)

theorem spectralMacdonald_reciprocal_point {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (t : ℝ) :
    (Complex.exp (-((x*y/z : ℝ) : ℂ)/2-
      ((x : ℂ)^2+(y : ℂ)^2)/(2*((x*y/z : ℝ) : ℂ)))*
      schlafliBesselK ((t : ℂ)*Complex.I) (x*y/(x*y/z)))/(z : ℂ) =
        spectralMacdonaldReciprocalIntegrand x y t z := by
  have hK : x*y/(x*y/z) = z := by field_simp
  rw [hK]
  unfold spectralMacdonaldReciprocalIntegrand
  congr 2
  push_cast
  field_simp
  ring_nf

theorem spectralMacdonaldReciprocalIntegrand_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    IntegrableOn (spectralMacdonaldReciprocalIntegrand x y t) (Ioi (0 : ℝ)) := by
  let F : ℝ → ℂ := fun r => Complex.exp (-(r : ℂ)/2-((x : ℂ)^2+(y : ℂ)^2)/(2*r))*
    schlafliBesselK ((t : ℂ)*Complex.I) (x*y/r)
  have hF : IntegrableOn (fun r => F r/(r : ℂ)) (Ioi (0 : ℝ)) := by
    apply (spectralMacdonaldProductIntegrand_integrable hx hy t).congr
    filter_upwards with r
    unfold F spectralMacdonaldProductIntegrand
    ring_nf
  have hi := (spectral_multiplicative_inverse_integrable F (mul_pos hx hy)).mpr hF
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact spectralMacdonald_reciprocal_point hx hy hz t

theorem schlafliBesselK_imaginary_reciprocal_product {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    (∫ z in Ioi (0 : ℝ), spectralMacdonaldReciprocalIntegrand x y t z) =
      2*schlafliBesselK ((t : ℂ)*Complex.I) x*schlafliBesselK ((t : ℂ)*Complex.I) y := by
  let F : ℝ → ℂ := fun r => Complex.exp (-(r : ℂ)/2-((x : ℂ)^2+(y : ℂ)^2)/(2*r))*
    schlafliBesselK ((t : ℂ)*Complex.I) (x*y/r)
  calc
    _ = ∫ z in Ioi (0 : ℝ), F (x*y/z)/(z : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      exact (spectralMacdonald_reciprocal_point hx hy hz t).symm
    _ = ∫ r in Ioi (0 : ℝ), F r/(r : ℂ) := spectral_multiplicative_inverse_integral F (mul_pos hx hy)
    _ = ∫ r in Ioi (0 : ℝ), spectralMacdonaldProductIntegrand x y t r := by
      apply integral_congr_ae
      filter_upwards with r
      unfold F spectralMacdonaldProductIntegrand
      ring_nf
    _ = _ := schlafliBesselK_imaginary_macdonald_product hx hy t

end ArtinMatthews
