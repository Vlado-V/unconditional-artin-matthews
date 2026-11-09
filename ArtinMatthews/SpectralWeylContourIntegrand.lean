module

public import ArtinMatthews.SpectralBesselPositiveOrderBound
public import ArtinMatthews.SpectralBesselJOrderAnalytic
public import ArtinMatthews.SpectralABLCorrectedWindows
public import ArtinMatthews.SpectralKLGaussianData


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Complex
noncomputable section

/-- The order integral obtained after the literal positive KL density is cancelled. -/
def spectralWeylContourIntegrand (cylinder : ℂ → ℝ → ℂ) (H : ℂ → ℂ)
    (R X : ℝ) (z : ℂ) : ℂ :=
  z * H z * Complex.exp (-2*(z/(R : ℂ))^2) * cylinder (-2*I*z) X

theorem spectralWeylGaussian_eq_square (R : ℝ) (z : ℂ) :
    Complex.exp (-2*(z/(R : ℂ))^2) = (spectralKLGaussianData R z)^2 := by
  simp only [spectralKLGaussianData, pow_two]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem spectralWeylGaussian_norm_bound {R : ℝ} (hR : 1 ≤ R) (t y : ℝ)
    (hy : |y| ≤ 5/8) :
    ‖Complex.exp (-2*(((t : ℂ)+(y : ℂ)*I)/(R : ℂ))^2)‖ ≤ Real.exp (25/32) := by
  have hRpos : 0 < R := by linarith
  have hy2 : y^2 ≤ (5/8 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) (by norm_num)).mpr hy
  rw [spectralWeylGaussian_eq_square, norm_pow, spectralKLGaussianData_norm_shift,
    pow_two, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hRy : (y/R)^2 ≤ (5/8 : ℝ)^2 := by
    rw [div_pow]
    exact (div_le_div_of_nonneg_right hy2 (sq_nonneg R)).trans
      (div_le_self (by norm_num) (by nlinarith))
  nlinarith [sq_nonneg (t/R)]

theorem spectralWeylContourIntegrand_differentiableAt
    (cylinder : ℂ → ℝ → ℂ) (H : ℂ → ℂ) (R X : ℝ) (z : ℂ)
    (hH : DifferentiableAt ℂ H z)
    (hCylinder : DifferentiableAt ℂ (fun ν => cylinder ν X) (-2*I*z)) :
    DifferentiableAt ℂ (spectralWeylContourIntegrand cylinder H R X) z := by
  have hC := hCylinder.comp z ((differentiableAt_id.const_mul (-2*I)))
  have hG : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-2*(w/(R : ℂ))^2)) z := by
    fun_prop
  exact ((differentiableAt_id.mul hH).mul hG).mul hC

theorem spectralWeylContourIntegrand_norm_le
    (cylinder : ℂ → ℝ → ℂ) (H base : ℂ → ℂ) (R X t y : ℝ)
    (_hX : 0 < X) (hy : 0 ≤ y)
    (hH : H ((t : ℂ)+(y : ℂ)*I) =
      base ((t : ℂ)+(y : ℂ)*I)*spectralABLCoshCancellation ((t : ℂ)+(y : ℂ)*I))
    (hCylinder : ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖) :
    ‖spectralWeylContourIntegrand cylinder H R X ((t : ℂ)+(y : ℂ)*I)‖ ≤
      ‖(t : ℂ)+(y : ℂ)*I‖ * ‖base ((t : ℂ)+(y : ℂ)*I)‖ *
        ‖Complex.exp (-2*(((t : ℂ)+(y : ℂ)*I)/(R : ℂ))^2)‖ *
        ((X/2)^(2*y)*Real.exp (X^2/4)) *
        ‖spectralABLCoshCancellation ((t : ℂ)+(y : ℂ)*I) /
          Complex.Gamma (1-2*I*((t : ℂ)+(y : ℂ)*I))‖ := by
  let z : ℂ := (t : ℂ)+(y : ℂ)*I
  have hre : (-2*I*z).re = 2*y := by
    dsimp [z]
    norm_num [Complex.mul_re, Complex.mul_im]
  have hbound := hCylinder (-2*I*z) (by rw [hre]; positivity)
  rw [hre, show -2*I*z+1 = 1-2*I*z by ring] at hbound
  change ‖z*H z*Complex.exp (-2*(z/(R : ℂ))^2)*cylinder (-2*I*z) X‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul, hH, norm_mul]
  calc
    _ ≤ (‖z‖*(‖base z‖*‖spectralABLCoshCancellation z‖)*
        ‖Complex.exp (-2*(z/(R : ℂ))^2)‖)*
        ((X/2)^(2*y)*Real.exp (X^2/4)/‖Complex.Gamma (1-2*I*z)‖) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by rw [norm_div]; ring

theorem spectralWeylJContour_differentiableAt (H : ℂ → ℂ) (R : ℝ) {X : ℝ}
    (hX : 0 < X) {z : ℂ} (hz : 0 ≤ z.im) (hH : DifferentiableAt ℂ H z) :
    DifferentiableAt ℂ (spectralWeylContourIntegrand (fun ν X => Complex.besselJ ν X) H R X) z := by
  apply spectralWeylContourIntegrand_differentiableAt _ _ _ _ _ hH
  exact spectral_besselJ_order_differentiableAt hX (by norm_num [Complex.mul_re, Complex.mul_im]; linarith)

theorem spectralWeylIContour_differentiableAt (H : ℂ → ℂ) (R : ℝ) {X : ℝ}
    (hX : 0 < X) {z : ℂ} (hz : 0 ≤ z.im) (hH : DifferentiableAt ℂ H z) :
    DifferentiableAt ℂ (spectralWeylContourIntegrand spectralBesselI H R X) z := by
  apply spectralWeylContourIntegrand_differentiableAt _ _ _ _ _ hH
  exact spectralBesselI_order_differentiableAt hX (by norm_num [Complex.mul_re, Complex.mul_im]; linarith)

end
end ArtinMatthews
