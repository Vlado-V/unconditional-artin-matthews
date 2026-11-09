module

public import ArtinMatthews.SpectralAntiKMellinKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Mellin integral of exp(x)K_nu(x), on
|Re nu| < Re s < 1/2.  Both half-line order terms are kept explicitly. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralAntiKMellinKernel_pair (ν s : ℂ) (u x : ℝ) :
    spectralAntiKMellinKernel ν s u x+spectralAntiKMellinKernel (-ν) s u x =
      (2*((x : ℂ)^(s-1)*Complex.exp (x : ℂ)))*spectralKCoshKernel ν x u := by
  unfold spectralAntiKMellinKernel spectralKCoshKernel
  have he : Complex.exp (-((Real.cosh u-1 : ℝ) : ℂ)*(x : ℂ)) =
      Complex.exp (x : ℂ)*Complex.exp ((-(x*Real.cosh u) : ℝ) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  have hc := Complex.two_cosh (ν*(u : ℂ))
  rw [neg_mul]
  linear_combination -((x : ℂ)^(s-1)*Complex.exp (x : ℂ)*
    Complex.exp ((-(x*Real.cosh u) : ℝ) : ℂ))*hc

theorem spectralAntiKMellinKernel_integral_u (ν s : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ u in Ioi (0 : ℝ),
      spectralAntiKMellinKernel ν s u x+spectralAntiKMellinKernel (-ν) s u x) =
      2*((x : ℂ)^(s-1)*Complex.exp (x : ℂ)*schlafliBesselK ν x) := by
  simp_rw [spectralAntiKMellinKernel_pair]
  rw [integral_const_mul,← schlafliBesselK_cosh_integral ν hx]
  ring

theorem spectralAntiK_mellin_integrable (ν s : ℂ)
    (hs : |ν.re| < s.re) (hsh : s.re < 1/2) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(s-1)*Complex.exp (x : ℂ)*schlafliBesselK ν x)
      (Ioi (0 : ℝ)) := by
  have hneg : |(-ν).re| < s.re := by simpa only [Complex.neg_re,abs_neg] using hs
  have hi := ((spectralAntiKMellinKernel_integrable ν s hs hsh).add
    (spectralAntiKMellinKernel_integrable (-ν) s hneg hsh)).integral_prod_right
  apply (hi.const_mul (1/2 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  dsimp only [Pi.add_apply,Prod.fst,Prod.snd]
  rw [spectralAntiKMellinKernel_integral_u ν s hx]
  ring

theorem spectralAntiK_mellin_beta (ν s : ℂ)
    (hs : |ν.re| < s.re) (hsh : s.re < 1/2) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (x : ℂ)*schlafliBesselK ν x) =
      (1/2 : ℂ)*Complex.Gamma s*(2 : ℂ)^s*
        (Complex.betaIntegral (s-ν) (1-2*s)+Complex.betaIntegral (s+ν) (1-2*s)) := by
  have hneg : |(-ν).re| < s.re := by simpa only [Complex.neg_re,abs_neg] using hs
  have hs0 : 0 < s.re := (abs_nonneg ν.re).trans_lt hs
  have hsum := (spectralAntiKMellinKernel_integrable ν s hs hsh).add
    (spectralAntiKMellinKernel_integrable (-ν) s hneg hsh)
  have hswap := integral_integral_swap
    (f := fun u x : ℝ => spectralAntiKMellinKernel ν s u x+spectralAntiKMellinKernel (-ν) s u x) hsum
  have hleft : (∫ u in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ),
      spectralAntiKMellinKernel ν s u x+spectralAntiKMellinKernel (-ν) s u x) =
      Complex.Gamma s*(2 : ℂ)^s*
        (Complex.betaIntegral (s-ν) (1-2*s)+Complex.betaIntegral (s+ν) (1-2*s)) := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), Complex.Gamma s*
          (spectralAntiCoshBetaProfile s ν u+spectralAntiCoshBetaProfile s (-ν) u) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        dsimp only
        rw [integral_add (spectralAntiKMellinKernel_slice_integrable ν s hs0 hu)
          (spectralAntiKMellinKernel_slice_integrable (-ν) s hs0 hu),
          spectralAntiKMellinKernel_integral_x ν s hs0 hu,
          spectralAntiKMellinKernel_integral_x (-ν) s hs0 hu]
        ring
      _ = _ := by
        rw [integral_const_mul,integral_add
          (spectralAntiCoshBetaProfile_integrable s ν ((le_abs_self ν.re).trans_lt hs) hsh)
          (spectralAntiCoshBetaProfile_integrable s (-ν) (by
            simp only [Complex.neg_re]
            linarith [neg_le_abs ν.re]) hsh),
          spectralAntiCoshBetaProfile_integral,spectralAntiCoshBetaProfile_integral]
        simp only [sub_neg_eq_add]
        ring
  have hright : (∫ x in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ),
      spectralAntiKMellinKernel ν s u x+spectralAntiKMellinKernel (-ν) s u x) =
      2*(∫ x in Ioi (0 : ℝ), (x : ℂ)^(s-1)*Complex.exp (x : ℂ)*schlafliBesselK ν x) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact spectralAntiKMellinKernel_integral_u ν s hx
  rw [hleft,hright] at hswap
  linear_combination -hswap/2

end ArtinMatthews
