module

public import ArtinMatthews.SpectralDampedKMellinKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Mellin transform of exp(-x)K_nu(x), obtained by absolute
Laplace/cosh Fubini and the proved beta log integral. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralDampedK_mellin_integrable (ν s : ℂ) (hs : |ν.re| < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*schlafliBesselK ν x)
      (Ioi (0 : ℝ)) := by
  have hi := (spectralDampedKMellinKernel_integrable ν s hs).integral_prod_right
  apply (hi.const_mul (1/2 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [spectralDampedKMellinKernel_integral_u ν s hx]
  ring_nf

theorem spectralDampedK_mellin_beta (ν s : ℂ) (hs : |ν.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*schlafliBesselK ν x) =
      (1/2 : ℂ)*Complex.Gamma s*(2 : ℂ)^s*Complex.betaIntegral (s+ν) (s-ν) := by
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  have h := integral_integral_swap (f := fun u x : ℝ => spectralDampedKMellinKernel ν s u x)
    (spectralDampedKMellinKernel_integrable ν s hs)
  have hleft : (∫ u : ℝ, ∫ x in Ioi (0 : ℝ), spectralDampedKMellinKernel ν s u x) =
      Complex.Gamma s*(2 : ℂ)^s*Complex.betaIntegral (s+ν) (s-ν) := by
    simp_rw [spectralDampedKMellinKernel_integral_x ν s hs0]
    rw [integral_const_mul,spectralCoshBetaProfile_integral]
    ring_nf
  have hright : (∫ x in Ioi (0 : ℝ), ∫ u : ℝ, spectralDampedKMellinKernel ν s u x) =
      2*(∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*schlafliBesselK ν x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact spectralDampedKMellinKernel_integral_u ν s hx
  rw [hleft,hright] at h
  linear_combination -h/2

theorem spectralDampedK_mellin (ν s : ℂ) (hs : |ν.re| < s.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (-(x : ℂ))*schlafliBesselK ν x) =
      (Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (s-ν)/Complex.Gamma (s+1/2) := by
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  have ha : 0 < (s+ν).re := by simp only [Complex.add_re]; linarith [neg_le_abs ν.re]
  have hb : 0 < (s-ν).re := by simp only [Complex.sub_re]; linarith [le_abs_self ν.re]
  have hG2 : Complex.Gamma (2*s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using mul_pos two_pos hs0)
  have hGh : Complex.Gamma (s+1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num; linarith)
  have hdup := Complex.Gamma_mul_Gamma_add_half s
  have hratio : Complex.Gamma s/Complex.Gamma (2*s) =
      (2 : ℂ)^(1-2*s)*(Real.sqrt Real.pi : ℂ)/Complex.Gamma (s+1/2) := by
    apply (div_eq_div_iff hG2 hGh).mpr
    rw [hdup]
    ring_nf
  have hp : (1/2 : ℂ)*(2 : ℂ)^s*(2 : ℂ)^(1-2*s) = (2 : ℂ)^(-s) := by
    rw [mul_assoc,← Complex.cpow_add _ _ (by norm_num),show s+(1-2*s) = 1+(-s) by ring,
      Complex.cpow_add _ _ (by norm_num),Complex.cpow_one]
    ring_nf
  rw [spectralDampedK_mellin_beta ν s hs,Complex.betaIntegral_eq_Gamma_mul_div _ _ ha hb,
    show s+ν+(s-ν) = 2*s by ring]
  calc
    _ = ((1/2 : ℂ)*(2 : ℂ)^s)*(Complex.Gamma s/Complex.Gamma (2*s))*
        Complex.Gamma (s+ν)*Complex.Gamma (s-ν) := by ring_nf
    _ = _ := by
      rw [hratio]
      linear_combination (Complex.Gamma (s+ν)*Complex.Gamma (s-ν)*(Real.sqrt Real.pi : ℂ)/Complex.Gamma (s+1/2))*hp

end ArtinMatthews
