module

public import ArtinMatthews.SpectralWeberKNormalization
public import ArtinMatthews.SpectralWeylGaussianKAction


set_option backward.privateInPublic true
@[expose] public section

/-! Exact opposite-sign K multiplier under Gaussian modulus testing.
The geometric side keeps the already proved modulus-first integration order. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeylKMultiplier_gaussian_integrable (r : ℝ) {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun X : ℝ => Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (8*(Real.cosh (Real.pi*r) : ℂ)*schlafliBesselK (2*((r : ℂ)*Complex.I)) X/(X : ℂ)))
      (Ioi (0 : ℝ)) := by
  have hν : |((r : ℂ)*Complex.I).re| < 1/2 := by norm_num
  have hi := (spectralWeberK_integrable hν hp).const_mul (8*(Real.cosh (Real.pi*r) : ℂ))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  field_simp [Complex.ofReal_ne_zero.mpr hX.ne']

theorem spectralWeylKMultiplier_gaussian (r : ℝ) {p : ℝ} (hp : 0 < p) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (8*(Real.cosh (Real.pi*r) : ℂ)*schlafliBesselK (2*((r : ℂ)*Complex.I)) X/(X : ℂ))) =
      2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((1/(8*p) : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) := by
  have he : (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
      (8*(Real.cosh (Real.pi*r) : ℂ)*schlafliBesselK (2*((r : ℂ)*Complex.I)) X/(X : ℂ))) =
      (8*(Real.cosh (Real.pi*r) : ℂ))*
        (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*
          schlafliBesselK (2*((r : ℂ)*Complex.I)) X) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro X hX
    dsimp only
    field_simp [Complex.ofReal_ne_zero.mpr hX.ne']
  rw [he,schlafliBesselK_imaginary_gaussian_weber r hp]
  have hc : (Real.cosh (Real.pi*r) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    have h := Real.one_le_cosh (Real.pi*r)
    linarith
  field_simp [hc]
  ring_nf

theorem spectralWeylGaussian_opposite_K_multiplier {x p : ℝ} (hx : 0 < x) (hp : 0 < p)
    (s t r : ℝ) (hs : s^2 = 1) (ht : t^2 = 1) (hst : s*t = -1) :
    (∫ z in Ioi (0 : ℝ),
      ((∫ X in Ioi (0 : ℝ), Real.exp (-p*X^2)*X*spectralWeylDimensionlessKernel s t X x z : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) z/(z : ℂ)) =
      schlafliBesselK ((r : ℂ)*Complex.I) x*
        (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*
          (8*(Real.cosh (Real.pi*r) : ℂ)*schlafliBesselK (2*((r : ℂ)*Complex.I)) X/(X : ℂ))) := by
  rw [spectralWeylGaussian_K_action hx hp s t r hs ht,spectralWeylKMultiplier_gaussian r hp,hst]
  norm_num only [neg_neg,one_div]
  ring

end ArtinMatthews
