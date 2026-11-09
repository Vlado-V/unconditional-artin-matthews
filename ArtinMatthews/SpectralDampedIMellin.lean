module

public import ArtinMatthews.SpectralBesselIUnitIntegral
public import ArtinMatthews.SpectralBetaLaplaceKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The Mellin transform of exp(-x)I_nu(x), with genuine absolute
beta/Laplace Fubini on its natural strip. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralDampedI_mellin_kernel (ν s : ℂ) {x : ℝ} (hx : 0 < x)
    (hν : -(1/2 : ℝ) < ν.re) :
    (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*spectralBesselI ν x =
      ((2 : ℂ)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2)))*
      ∫ t in Ioo (0 : ℝ) 1,
        spectralBetaLaplaceKernel (ν+1/2) (ν+1/2) (s+ν) t x := by
  rw [mul_assoc,spectralBesselI_damped_unit_integral ν hx hν]
  have hp : (x : ℂ)^(s-1)*(x : ℂ)^ν = (x : ℂ)^(s+ν-1) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 1
    ring_nf
  calc
    _ = ((2 : ℂ)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2)))*
        ((x : ℂ)^(s+ν-1)*∫ t in Ioo (0 : ℝ) 1,
          Complex.exp ((-2*x*t : ℝ) : ℂ)*spectralUnitBetaProfile (ν+1/2) (ν+1/2) t) := by
      rw [← hp]
      ring_nf
    _ = _ := by
      congr 1
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t _
      unfold spectralBetaLaplaceKernel
      dsimp only
      have he : ((-2*x*t : ℝ) : ℂ) = -((2*t : ℝ) : ℂ)*(x : ℂ) := by push_cast; ring_nf
      rw [he]
      ring_nf

theorem spectralDampedI_mellin_integrable (ν s : ℂ)
    (hν : -(1/2 : ℝ) < ν.re) (hleft : 0 < (s+ν).re) (hright : s.re < 1/2) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*spectralBesselI ν x)
      (Ioi (0 : ℝ)) := by
  have ha : 0 < ((ν+1/2)-(s+ν)).re := by
    norm_num
    linarith
  have hb : 0 < (ν+(1/2 : ℂ)).re := by norm_num; linarith
  have hi := (spectralBetaLaplaceKernel_integrable (ν+1/2) (ν+1/2) (s+ν)
    hleft ha hb).integral_prod_right
  apply (hi.const_mul ((2 : ℂ)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2)))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (spectralDampedI_mellin_kernel ν s hx hν).symm

theorem spectralDampedI_mellin_beta (ν s : ℂ)
    (hν : -(1/2 : ℝ) < ν.re) (hleft : 0 < (s+ν).re) (hright : s.re < 1/2) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*spectralBesselI ν x) =
      (2 : ℂ)^(-s)*Complex.Gamma (s+ν)/
        ((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2))*
          Complex.betaIntegral (1/2-s) (ν+1/2) := by
  have ha : 0 < ((ν+1/2)-(s+ν)).re := by norm_num; linarith
  have hb : 0 < (ν+(1/2 : ℂ)).re := by norm_num; linarith
  calc
    _ = ((2 : ℂ)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2)))*
        ∫ x in Ioi (0 : ℝ), ∫ t in Ioo (0 : ℝ) 1,
          spectralBetaLaplaceKernel (ν+1/2) (ν+1/2) (s+ν) t x := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact spectralDampedI_mellin_kernel ν s hx hν
    _ = _ := by
      rw [spectralBetaLaplaceKernel_integral _ _ _ hleft ha hb,
        show ν+(1/2 : ℂ)-(s+ν) = 1/2-s by ring]
      have hp : (2 : ℂ)^ν*(2 : ℂ)^(-(s+ν)) = (2 : ℂ)^(-s) := by
        rw [← Complex.cpow_add _ _ (by norm_num)]
        congr 1
        ring_nf
      calc
        _ = ((2 : ℂ)^ν*(2 : ℂ)^(-(s+ν)))*Complex.Gamma (s+ν)/
            ((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2))*
            Complex.betaIntegral (1/2-s) (ν+1/2) := by ring_nf
        _ = _ := by rw [hp]

theorem spectralDampedI_mellin (ν s : ℂ)
    (hν : -(1/2 : ℝ) < ν.re) (hleft : 0 < (s+ν).re) (hright : s.re < 1/2) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*spectralBesselI ν x) =
      (2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (1/2-s)/
        ((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1-s)) := by
  have ha : 0 < ((1/2 : ℂ)-s).re := by norm_num; linarith
  have hb : 0 < (ν+(1/2 : ℂ)).re := by norm_num; linarith
  have hG : Complex.Gamma (ν+1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hb
  rw [spectralDampedI_mellin_beta ν s hν hleft hright,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ ha hb,
    show (1/2 : ℂ)-s+(ν+1/2) = ν+1-s by ring]
  simp only [div_eq_mul_inv,mul_inv]
  calc
    _ = ((2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (1/2-s)*
        ((Real.sqrt Real.pi : ℂ)⁻¹*(Complex.Gamma (ν+1-s))⁻¹))*
        (Complex.Gamma (ν+1/2)*(Complex.Gamma (ν+1/2))⁻¹) := by ring_nf
    _ = _ := by
      rw [mul_inv_cancel₀ hG,mul_one]
      simp only [one_div,one_mul]

end ArtinMatthews
