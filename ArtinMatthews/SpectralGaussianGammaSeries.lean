module

public import ArtinMatthews.SpectralGaussianRealMoment
public import ArtinMatthews.SpectralKummerSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute Gaussian integration of the confluent gamma series.
The summed norm integrals are controlled by the actual entire hypergeometric series. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators

namespace ArtinMatthews

def spectralGaussianGammaTerm (a b z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (z^n/((n.factorial : ℂ)*Complex.Gamma (b+n)))*
    ((x : ℂ)^(2*(a+n)-1)*Complex.exp (-(x : ℂ)^2))

theorem spectralGaussianGammaTerm_integrable (a b z : ℂ) (ha : 0 < a.re) (n : ℕ) :
    IntegrableOn (spectralGaussianGammaTerm a b z n) (Ioi (0 : ℝ)) := by
  have hs : 0 < (2*(a+(n : ℂ))).re := by
    norm_num [Complex.mul_re]
    positivity
  have h := (spectralGaussianMellin_integrable (2*(a+n)) hs (p := 1) (by norm_num)).const_mul
    (z^n/((n.factorial : ℂ)*Complex.Gamma (b+n)))
  simpa only [spectralGaussianGammaTerm,Complex.ofReal_one,neg_mul,one_mul] using! h

theorem spectralGaussianGammaTerm_integral (a b z : ℂ) (ha : 0 < a.re) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), spectralGaussianGammaTerm a b z n x) =
      (1/2 : ℂ)*(Complex.Gamma (a+n)*z^n/((n.factorial : ℂ)*Complex.Gamma (b+n))) := by
  have hs : 0 < (2*(a+(n : ℂ))).re := by norm_num [Complex.mul_re]; positivity
  unfold spectralGaussianGammaTerm
  rw [integral_const_mul]
  have h := spectralGaussianMellin_integral (2*(a+n)) hs (p := 1) (by norm_num)
  rw [show 2*(a+(n : ℂ))/2 = a+n by ring] at h
  norm_num only [Complex.ofReal_one,one_div,inv_one,Complex.one_cpow,mul_one] at h
  rw [show (∫ x in Ioi (0 : ℝ), (x : ℂ)^(2*(a+n)-1)*Complex.exp (-(x : ℂ)^2)) =
      (1/2 : ℂ)*Complex.Gamma (a+n) by simpa only [neg_mul,one_mul] using h]
  ring

theorem spectralGaussianGammaTerm_integral_norm (a b z : ℂ) (ha : 0 < a.re) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖spectralGaussianGammaTerm a b z n x‖) =
      (1/2 : ℝ)*‖z^n/((n.factorial : ℂ)*Complex.Gamma (b+n))‖*Real.Gamma (a.re+n) := by
  calc
    _ = ‖z^n/((n.factorial : ℂ)*Complex.Gamma (b+n))‖*
        (∫ x in Ioi (0 : ℝ), x^(2*(a.re+n)-1)*Real.exp (-x^2)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only [spectralGaussianGammaTerm]
      rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.norm_exp]
      norm_num [Complex.mul_re]
      simp only [← Complex.ofReal_pow,Complex.ofReal_re,true_or]
    _ = _ := by rw [spectralGaussianRealMoment (by positivity)]; ring

theorem spectralGaussianGammaTerm_norm_summable (a b z : ℂ) (ha : 0 < a.re) :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖spectralGaussianGammaTerm a b z n x‖) := by
  have h := (spectralKummer_gamma_summable (a.re : ℂ) b (‖z‖ : ℂ) ha).norm.mul_left (1/2 : ℝ)
  apply h.congr
  intro n
  rw [spectralGaussianGammaTerm_integral_norm a b z ha n]
  have harg : (a.re : ℂ)+(n : ℂ) = ((a.re+n : ℝ) : ℂ) := by push_cast; rfl
  have hG : ‖Complex.Gamma ((a.re : ℂ)+(n : ℂ))‖ = Real.Gamma (a.re+n) := by
    rw [harg,Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos (by positivity))]
  simp only [norm_div,norm_mul,norm_pow,Complex.norm_natCast,hG,Complex.norm_real,
    Real.norm_eq_abs,abs_norm]
  ring

theorem spectralGaussianGammaSeries_integral (a b z : ℂ) (ha : 0 < a.re) :
    (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, spectralGaussianGammaTerm a b z n x) =
      (1/2 : ℂ)*∑' n : ℕ, Complex.Gamma (a+n)*z^n/((n.factorial : ℂ)*Complex.Gamma (b+n)) := by
  rw [← integral_tsum_of_summable_integral_norm
    (spectralGaussianGammaTerm_integrable a b z ha) (spectralGaussianGammaTerm_norm_summable a b z ha)]
  simp_rw [spectralGaussianGammaTerm_integral a b z ha]
  exact tsum_mul_left

end ArtinMatthews
