module

public import ArtinMatthews.SpectralBesselImaginaryMeasurable
public import ArtinMatthews.SpectralWeylMultiplierMajorant
public import ArtinMatthews.SpectralWeylGaussianKNegative


set_option backward.privateInPublic true
@[expose] public section

/-! Literal positive-modulus J/K Weyl multipliers, their proved joint
measurability, order majorants, and evaluated Gaussian integrals. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralWeylJMultiplier (r X : ℝ) : ℂ :=
  if 0 < X then ((2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*r) : ℂ))*
    (Complex.besselJ (((2*r : ℝ) : ℂ)*Complex.I) (X : ℂ)-
      Complex.besselJ (((-2*r : ℝ) : ℂ)*Complex.I) (X : ℂ))/(X : ℂ) else 0

def spectralWeylKMultiplier (r X : ℝ) : ℂ :=
  if 0 < X then 8*(Real.cosh (Real.pi*r) : ℂ)*
    schlafliBesselK (((2*r : ℝ) : ℂ)*Complex.I) X/(X : ℂ) else 0

theorem spectralWeylJMultiplier_measurable : Measurable (fun p : ℝ × ℝ => spectralWeylJMultiplier p.1 p.2) := by
  have hp := spectral_besselJ_imaginary_positive_joint_measurable 2
  have hm := spectral_besselJ_imaginary_positive_joint_measurable (-2)
  have he : (fun p : ℝ × ℝ => spectralWeylJMultiplier p.1 p.2) =
      fun p : ℝ × ℝ => ((2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*p.1) : ℂ))*
        ((if 0 < p.2 then Complex.besselJ (((2*p.1 : ℝ) : ℂ)*Complex.I) (p.2 : ℂ) else 0)-
          (if 0 < p.2 then Complex.besselJ (((-2*p.1 : ℝ) : ℂ)*Complex.I) (p.2 : ℂ) else 0))/(p.2 : ℂ) := by
    funext p
    by_cases hx : 0 < p.2
    · simp only [spectralWeylJMultiplier, ite_eq_left hx]
    · simp only [spectralWeylJMultiplier, ite_eq_right hx, sub_self, mul_zero, zero_div]
  rw [he]
  exact ((by fun_prop : Measurable (fun p : ℝ × ℝ =>
    (2*(Real.pi : ℂ)*Complex.I)/(Real.sinh (Real.pi*p.1) : ℂ))).mul (hp.sub hm)).div (by fun_prop)

theorem spectralWeylKMultiplier_measurable : Measurable (fun p : ℝ × ℝ => spectralWeylKMultiplier p.1 p.2) := by
  have hm := spectral_besselK_imaginary_positive_joint_measurable.comp
    (show Measurable (fun p : ℝ × ℝ => (2*p.1,p.2)) by fun_prop)
  have he : (fun p : ℝ × ℝ => spectralWeylKMultiplier p.1 p.2) =
      fun p : ℝ × ℝ => 8*(Real.cosh (Real.pi*p.1) : ℂ)*
        (if 0 < p.2 then schlafliBesselK (((2*p.1 : ℝ) : ℂ)*Complex.I) p.2 else 0)/(p.2 : ℂ) := by
    funext p
    by_cases hx : 0 < p.2
    · simp only [spectralWeylKMultiplier, ite_eq_left hx]
    · simp only [spectralWeylKMultiplier, ite_eq_right hx, mul_zero, zero_div]
  rw [he]
  exact ((by fun_prop : Measurable (fun p : ℝ × ℝ => 8*(Real.cosh (Real.pi*p.1) : ℂ))).mul hm).div (by fun_prop)

theorem spectralWeylJMultiplier_order_bound {r X : ℝ} (hr : 0 < r) (hX : 0 < X) :
    ‖(X : ℂ)*spectralWeylJMultiplier r X‖ ≤
      4*Real.pi*Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/r) := by
  rw [spectralWeylJMultiplier,ite_eq_left hX,
    show (((2*r : ℝ) : ℂ)*Complex.I) = 2*((r : ℂ)*Complex.I) by push_cast; ring,
    show (((-2*r : ℝ) : ℂ)*Complex.I) = 2*(-((r : ℂ)*Complex.I)) by push_cast; ring]
  exact spectralWeylJMultiplier_order_majorant hr hX

theorem spectralWeylKMultiplier_order_bound {r X : ℝ} (hr : 0 < r) (hX : 0 < X) :
    ‖(X : ℂ)*spectralWeylKMultiplier r X‖ ≤
      4*Real.pi*Real.exp (X^2/4)*(1+(Real.sqrt (Real.cosh Real.pi)/Real.pi)/r) := by
  rw [spectralWeylKMultiplier,ite_eq_left hX,
    show (((2*r : ℝ) : ℂ)*Complex.I) = 2*((r : ℂ)*Complex.I) by push_cast; ring]
  exact spectralWeylKMultiplier_order_majorant hr hX

theorem spectralWeylJMultiplier_gaussian_value {r p : ℝ} (hr : 0 < r) (hp : 0 < p) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*spectralWeylJMultiplier r X) =
      2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp (-((1/(8*p) : ℝ) : ℂ))*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) := by
  convert spectralWeylJMultiplier_imaginary_gaussian hr hp using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [spectralWeylJMultiplier,ite_eq_left (show 0 < X from hX),
    show (((2*r : ℝ) : ℂ)*Complex.I) = 2*((r : ℂ)*Complex.I) by push_cast; ring,
    show (((-2*r : ℝ) : ℂ)*Complex.I) = 2*(-((r : ℂ)*Complex.I)) by push_cast; ring]

theorem spectralWeylKMultiplier_gaussian_value {r p : ℝ} (_hr : 0 < r) (hp : 0 < p) :
    (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*spectralWeylKMultiplier r X) =
      2*(Real.sqrt (Real.pi/p) : ℂ)*Complex.exp ((1/(8*p) : ℝ) : ℂ)*
        schlafliBesselK ((r : ℂ)*Complex.I) (1/(8*p)) := by
  convert spectralWeylKMultiplier_gaussian r hp using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [spectralWeylKMultiplier,ite_eq_left (show 0 < X from hX),
    show (((2*r : ℝ) : ℂ)*Complex.I) = 2*((r : ℂ)*Complex.I) by push_cast; ring]

end ArtinMatthews
