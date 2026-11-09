module

public import ArtinMatthews.SpectralKDerivativeAdjacentOrder
public import Mathlib.Analysis.Calculus.FDeriv.Measurable


set_option backward.privateInPublic true
@[expose] public section

/-! The checked Mellin product also controls the actual adjacent order
needed for the physical derivative. The estimate is uniform in the real
spectral parameter and has the literal hyperbolic cosine normalization. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein
open scoped ComplexConjugate

namespace ArtinMatthews

theorem spectralKAdjacentSquare_mellin_integrand (t x : ℝ) (hx : 0 < x) :
    (x : ℂ)^((3 : ℂ)-1)*schlafliBesselK (1+(t : ℂ)*Complex.I) x*
      schlafliBesselK (1-(t : ℂ)*Complex.I) x =
      ((x^2*‖schlafliBesselK (1+(t : ℂ)*Complex.I) x‖^2 : ℝ) : ℂ) := by
  let ν := (t : ℂ)*Complex.I
  have hν : star (1+ν) = 1-ν := by
    change conj (1+(t : ℂ)*Complex.I) = 1-(t : ℂ)*Complex.I
    simp only [map_add,map_one,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,sub_eq_add_neg]
  have hK : schlafliBesselK (1+ν) x*schlafliBesselK (1-ν) x =
      ((‖schlafliBesselK (1+ν) x‖^2 : ℝ) : ℂ) := by
    rw [← hν,← schlafliBesselK_star_order _ hx,mul_comm]
    change conj (schlafliBesselK (1+ν) x)*schlafliBesselK (1+ν) x = _
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  rw [show (3 : ℂ)-1 = ((2 : ℕ) : ℂ) by norm_num,Complex.cpow_natCast,mul_assoc,hK,
    Complex.ofReal_mul]
  simp only [Complex.ofReal_pow,ν]

theorem spectralKAdjacentSquare_integrable (t : ℝ) :
    IntegrableOn (fun x : ℝ => x^2*‖schlafliBesselK (1+(t : ℂ)*Complex.I) x‖^2) (Ioi 0) := by
  let ν := (t : ℂ)*Complex.I
  have h : |(1+ν).re|+|(1-ν).re| < (3 : ℂ).re := by
    dsimp only [ν]
    norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re]
  have hi := (schlafliBesselK_product_mellin_integrable_of_re_gt (1+ν) (1-ν) 3 h).re
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  dsimp only [ν]
  rw [spectralKAdjacentSquare_mellin_integrand t x hx]
  rfl

theorem spectralKAdjacentSquare_moment (t : ℝ) :
    (∫ x in Ioi (0 : ℝ), x^2*‖schlafliBesselK (1+(t : ℂ)*Complex.I) x‖^2) =
      (3/2)*(t^2+1/4)*spectralKSquareMoment 0 t := by
  let ν := (t : ℂ)*Complex.I
  let a : ℂ := 1/2
  have h : |(1+ν).re|+|(1-ν).re| < (3 : ℂ).re := by
    dsimp only [ν]
    norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re]
  have hI : ((∫ x in Ioi (0 : ℝ), x^2*‖schlafliBesselK (1+ν) x‖^2 : ℝ) : ℂ) =
      ∫ x in Ioi (0 : ℝ), (x : ℂ)^((3 : ℂ)-1)*schlafliBesselK (1+ν) x*schlafliBesselK (1-ν) x := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (spectralKAdjacentSquare_mellin_integrand t x hx).symm
  have ha : a ≠ 0 := by dsimp only [a]; norm_num
  have ham : a-ν ≠ 0 := ne_of_apply_ne Complex.re (by dsimp only [a,ν]; norm_num [Complex.sub_re,Complex.mul_re,Complex.div_re])
  have hap : a+ν ≠ 0 := ne_of_apply_ne Complex.re (by dsimp only [a,ν]; norm_num [Complex.add_re,Complex.mul_re,Complex.div_re])
  have ha1 : a+1 ≠ 0 := by dsimp only [a]; norm_num
  have hG3 : Complex.Gamma (3 : ℂ) = 2 := by norm_num
  have hG5 : Complex.Gamma (a+2) = (3/4 : ℂ)*Complex.Gamma a := by
    rw [show a+2 = (a+1)+1 by ring,Complex.Gamma_add_one _ ha1,Complex.Gamma_add_one _ ha]
    dsimp only [a]
    ring
  have hPoly : (a-ν)*(a+ν) = (t : ℂ)^2+1/4 := by
    dsimp only [a,ν]
    linear_combination -((t : ℂ)^2)*Complex.I_sq
  have hhalf : Complex.Gamma a*Complex.Gamma a = (Real.pi : ℂ) := by
    simpa [a] using spectral_Gamma_half_imaginary_product 0
  apply Complex.ofReal_injective
  rw [hI,schlafliBesselK_product_mellin_closed _ _ 3 h,
    show (3-(1+ν)-(1-ν))/2 = a by dsimp only [a]; ring,
    show (3+(1+ν)-(1-ν))/2 = (a+ν)+1 by dsimp only [a]; ring,
    show (3-(1+ν)+(1-ν))/2 = (a-ν)+1 by dsimp only [a]; ring,
    show (3+(1+ν)+(1-ν))/2 = a+2 by dsimp only [a]; ring,
    show (3-3 : ℂ) = 0 by norm_num,Complex.cpow_zero,one_mul,hG3,hG5,
    Complex.Gamma_add_one _ ham,Complex.Gamma_add_one _ hap]
  calc
    _ = (3/8 : ℂ)*((a-ν)*(a+ν))*(Complex.Gamma a*Complex.Gamma a)*
        (Complex.Gamma (a-ν)*Complex.Gamma (a+ν)) := by ring
    _ = _ := by
      rw [hPoly,hhalf,spectralKSquareMoment_zero]
      change (3/8 : ℂ)*((t : ℂ)^2+1/4)*(Real.pi : ℂ)*
          (Complex.Gamma ((1/2 : ℂ)-(t : ℂ)*Complex.I)*Complex.Gamma ((1/2 : ℂ)+(t : ℂ)*Complex.I)) = _
      rw [spectral_Gamma_half_imaginary_product]
      push_cast
      ring

theorem spectralKLRealKernel_deriv_square_integrable (t : ℝ) :
    IntegrableOn (fun x : ℝ => x^2*(deriv (spectralKLRealKernel t) x)^2) (Ioi 0) := by
  have hm : Measurable (fun x : ℝ => x^2*(deriv (spectralKLRealKernel t) x)^2) := by
    have hd : Measurable (deriv (spectralKLRealKernel t)) := measurable_deriv _
    fun_prop
  apply (spectralKAdjacentSquare_integrable t).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs,sq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) (spectralKLRealKernel_deriv_norm_le_adjacent t hx) 2) (sq_nonneg _)

theorem spectralKLRealKernel_deriv_square_moment_bound (t : ℝ) :
    (∫ x in Ioi (0 : ℝ), x^2*(deriv (spectralKLRealKernel t) x)^2) ≤
      (3/2)*(t^2+1/4)*spectralKSquareMoment 0 t := by
  rw [← spectralKAdjacentSquare_moment t]
  apply setIntegral_mono_on (spectralKLRealKernel_deriv_square_integrable t)
    (spectralKAdjacentSquare_integrable t) measurableSet_Ioi
  intro x hx
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs,sq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) (spectralKLRealKernel_deriv_norm_le_adjacent t hx) 2) (sq_nonneg _)

end ArtinMatthews
