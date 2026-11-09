module

public import ArtinMatthews.SpectralGammaStripBound
public import ArtinMatthews.SpectralBesselIShiftedBound


set_option backward.privateInPublic true
@[expose] public section

/-! A uniform order-strip estimate for the genuine I kernel, including
the vertical sides of a shifted inverse-KL contour. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralPoissonMajorant_integrable (c : ℝ) (hc : 0 ≤ c) :
    IntervalIntegrable (fun u : ℝ => ‖(1-(u : ℂ)^2)^((c : ℂ)-1/2)‖)
      volume (-1) 1 := by
  have hν : -(1/2 : ℝ) < (c : ℂ).re := by change -(1/2 : ℝ) < c;linarith
  have h := spectralPoissonMoment_integrable (c : ℂ) hν 0
  change IntervalIntegrable (fun u : ℝ => (u : ℂ)^0*(1-(u : ℂ)^2)^((c : ℂ)-1/2)) volume (-1) 1 at h
  simpa only [pow_zero,one_mul] using h.norm

theorem spectralPoissonMajorant_le_zero (c : ℝ) (hc : 0 ≤ c) :
    spectralPoissonMajorant c ≤ spectralPoissonMajorant 0 := by
  unfold spectralPoissonMajorant
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
    (spectralPoissonMajorant_integrable c hc) (spectralPoissonMajorant_integrable 0 le_rfl)
  intro u hu
  have hp : 0 < 1-u^2 := by nlinarith [hu.1,hu.2]
  have hcast : ((1-u^2 : ℝ) : ℂ) = 1-(u : ℂ)^2 := by push_cast;rfl
  rw [← hcast,Complex.norm_cpow_eq_rpow_re_of_pos hp,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  norm_num
  exact Real.rpow_le_rpow_of_exponent_ge hp (by nlinarith [sq_nonneg u]) (by linarith)

theorem spectralBesselI_closed_strip_exp_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ c t x : ℝ, 0 ≤ c → c ≤ B → 0 < x →
      ‖spectralBesselI ((c : ℂ)+(t : ℂ)*Complex.I) x‖ ≤
        C*(1+|t|)*Real.exp (x+Real.pi*|t|/2)*x^c := by
  obtain ⟨Cg,hCg,hGamma⟩ := spectral_inv_gamma_closed_strip_bound B hB
  let P := spectralPoissonMajorant 0
  have hP : 0 ≤ P := spectralPoissonMajorant_nonneg 0
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  refine ⟨Cg/Real.sqrt Real.pi*(P+1),by positivity,?_⟩
  intro c t x hc0 hcB hx
  let ν : ℂ := (c : ℂ)+(t : ℂ)*Complex.I
  have hνre : ν.re = c := by simp [ν,Complex.mul_re]
  have hν : -(1/2 : ℝ) < ν.re := by rw [hνre];linarith
  have harg : ν+1/2 = (((c+1/2 : ℝ) : ℂ)+(t : ℂ)*Complex.I) := by
    dsimp only [ν]
    push_cast
    ring
  have hg : ‖Complex.Gamma (ν+1/2)‖⁻¹ ≤ Cg*(1+|t|)*Real.exp (Real.pi*|t|/2) := by
    simpa only [← harg,norm_inv] using hGamma c t hc0 hcB
  have hnum : ‖(x/2 : ℂ)^ν‖ = (x/2)^c := by
    rw [show (x/2 : ℂ) = ((x/2 : ℝ) : ℂ) by push_cast;rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (half_pos hx),hνre]
  have hnum_le : (x/2)^c ≤ x^c := Real.rpow_le_rpow (by positivity) (by linarith) hc0
  have hi : ‖∫ u : ℝ in (-1 : ℝ)..1,Complex.exp ((-x*u : ℝ) : ℂ)*(1-(u : ℂ)^2)^(ν-1/2)‖ ≤
      Real.exp x*(P+1) := by
    exact (spectralBesselI_poisson_norm_bound c t x hc0 hx).trans
      (mul_le_mul_of_nonneg_left ((spectralPoissonMajorant_le_zero c hc0).trans (by dsimp only [P];linarith))
        (Real.exp_nonneg x))
  rw [spectralBesselI_poisson ν hx hν,norm_mul,norm_div,norm_mul,hnum,
    Complex.norm_of_nonneg (Real.sqrt_nonneg Real.pi)]
  calc
    _ = ((x/2)^c/Real.sqrt Real.pi)*‖Complex.Gamma (ν+1/2)‖⁻¹*
        ‖∫ u : ℝ in (-1 : ℝ)..1,Complex.exp ((-x*u : ℝ) : ℂ)*(1-(u : ℂ)^2)^(ν-1/2)‖ := by
      simp only [div_eq_mul_inv,mul_inv]
      ring
    _ ≤ (x^c/Real.sqrt Real.pi)*(Cg*(1+|t|)*Real.exp (Real.pi*|t|/2))*(Real.exp x*(P+1)) := by
      apply mul_le_mul
      · exact mul_le_mul (div_le_div_of_nonneg_right hnum_le hpi.le) hg
          (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
      · exact hi
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [Real.exp_add];ring

end ArtinMatthews
