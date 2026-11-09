module

public import ArtinMatthews.SpectralBesselI
public import ArtinMatthews.SpectralBesselPoissonBound


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine vertical-order I bound with exponential spatial growth.
The order normalization comes from the existing Beta/Gamma estimate. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralBesselI_poisson_norm_bound (c t x : ℝ) (hc : 0 ≤ c) (hx : 0 < x) :
    ‖∫ u : ℝ in (-1 : ℝ)..1, Complex.exp ((-x*u : ℝ) : ℂ)*
      (1-(u : ℂ)^2)^(((c : ℂ)+(t : ℂ)*Complex.I)-1/2)‖ ≤
      Real.exp x*spectralPoissonMajorant c := by
  have hw : IntervalIntegrable (fun u : ℝ => (1-(u : ℂ)^2)^((c : ℂ)-1/2)) volume (-1) 1 := by
    have hcν : -(1/2 : ℝ) < (c : ℂ).re := by
      change -(1/2 : ℝ) < c
      linarith
    have hh := spectralPoissonMoment_integrable (c : ℂ) hcν 0
    change IntervalIntegrable (fun u : ℝ => (u : ℂ)^0*(1-(u : ℂ)^2)^((c : ℂ)-1/2)) volume (-1) 1 at hh
    simpa only [pow_zero,one_mul] using hh
  have hg := hw.norm.const_mul (Real.exp x)
  have hb : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioc (-1 : ℝ) 1 →
      ‖Complex.exp ((-x*u : ℝ) : ℂ)*(1-(u : ℂ)^2)^(((c : ℂ)+(t : ℂ)*Complex.I)-1/2)‖ ≤
        Real.exp x*‖(1-(u : ℂ)^2)^((c : ℂ)-1/2)‖ := by
    filter_upwards [volume.ae_ne (1 : ℝ)] with u hne
    intro hu
    have hu1 : u < 1 := lt_of_le_of_ne hu.2 hne
    have hp : 0 < 1-u^2 := by nlinarith [hu.1,hu1]
    have hcast : ((1-u^2 : ℝ) : ℂ) = 1-(u : ℂ)^2 := by push_cast;rfl
    have he : ‖Complex.exp ((-x*u : ℝ) : ℂ)‖ ≤ Real.exp x := by
      rw [Complex.norm_exp,Complex.ofReal_re]
      apply Real.exp_le_exp.mpr
      nlinarith [hu.1]
    have hpow : ‖(1-(u : ℂ)^2)^(((c : ℂ)+(t : ℂ)*Complex.I)-1/2)‖ =
        ‖(1-(u : ℂ)^2)^((c : ℂ)-1/2)‖ := by
      rw [← hcast,Complex.norm_cpow_eq_rpow_re_of_pos hp,Complex.norm_cpow_eq_rpow_re_of_pos hp]
      congr 1
      norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re]
    rw [norm_mul,hpow]
    exact mul_le_mul_of_nonneg_right he (norm_nonneg _)
  have h := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (-1 : ℝ) ≤ 1) hb hg
  simpa only [intervalIntegral.integral_const_mul,spectralPoissonMajorant] using h

theorem spectralBesselI_vertical_exp_bound (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ t x : ℝ, 0 < x →
      ‖spectralBesselI ((c : ℂ)+(t : ℂ)*Complex.I) x‖ ≤
        C*Real.exp (x+Real.pi*|t|/2)*x^c := by
  obtain ⟨Cg,hCg,hGamma⟩ := spectral_inv_gamma_vertical_bound c hc
  let B := spectralPoissonMajorant c
  have hB : 0 ≤ B := spectralPoissonMajorant_nonneg c
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨Cg/Real.sqrt Real.pi*(B+1),by positivity,?_⟩
  intro t x hx
  let ν : ℂ := (c : ℂ)+(t : ℂ)*Complex.I
  have hνre : ν.re = c := by simp [ν,Complex.mul_re]
  have hν : -(1/2 : ℝ) < ν.re := by rw [hνre];linarith
  have harg : ν+1/2 = (((c+1/2 : ℝ) : ℂ)+2*(t/2 : ℝ)*Complex.I) := by
    dsimp only [ν]
    push_cast
    ring
  have habs : Real.pi*|t/2| = Real.pi*|t|/2 := by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  have hg : ‖Complex.Gamma (ν+1/2)‖⁻¹ ≤ Cg*Real.exp (Real.pi*|t|/2) := by
    simpa only [← harg,norm_inv,habs] using hGamma (t/2)
  have hnum : ‖(x/2 : ℂ)^ν‖ = (x/2)^c := by
    rw [show (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) by push_cast;rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (half_pos hx),hνre]
  have hnum_le : (x/2)^c ≤ x^c := Real.rpow_le_rpow (by positivity) (by linarith) hc
  have hi := spectralBesselI_poisson_norm_bound c t x hc hx
  change ‖∫ u : ℝ in (-1 : ℝ)..1, Complex.exp ((-x*u : ℝ) : ℂ)*(1-(u : ℂ)^2)^(ν-1/2)‖ ≤ Real.exp x*B at hi
  rw [spectralBesselI_poisson ν hx hν,norm_mul,norm_div,norm_mul,hnum,
    Complex.norm_of_nonneg (Real.sqrt_nonneg Real.pi)]
  calc
    _ = ((x/2)^c/Real.sqrt Real.pi)*‖Complex.Gamma (ν+1/2)‖⁻¹*
        ‖∫ u : ℝ in (-1 : ℝ)..1, Complex.exp ((-x*u : ℝ) : ℂ)*(1-(u : ℂ)^2)^(ν-1/2)‖ := by
      simp only [div_eq_mul_inv,mul_inv]
      ring
    _ ≤ (x^c/Real.sqrt Real.pi)*(Cg*Real.exp (Real.pi*|t|/2))*(Real.exp x*(B+1)) := by
      apply mul_le_mul
      · exact mul_le_mul (div_le_div_of_nonneg_right hnum_le hpi.le) hg
          (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
      · exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg x))
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [Real.exp_add];ring

end ArtinMatthews
