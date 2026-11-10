module

public import ArtinMatthews.SpectralWeberKMellinKernel
public import ArtinMatthews.SpectralWeberKBasic
public import ArtinMatthews.SpectralBesselMellinEvaluation
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Mellin transform of the Gaussian K integral, obtained by
absolute interchange and the already evaluated Schlaefli K Mellin integral. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralWeberKMellinKernel_integral_x (ν s : ℂ) (p : ℝ) :
    (∫ x in Ioi (0 : ℝ), spectralWeberKMellinKernel ν s x p) =
      (p : ℂ)^(s-1)*spectralWeberKTransform ν p := by
  unfold spectralWeberKMellinKernel spectralWeberKTransform
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  have he : -((x^2 : ℝ) : ℂ)*(p : ℂ) = -(p : ℂ)*(x : ℂ)^2 := by push_cast; ring
  rw [he]
  ring

theorem spectralWeberK_mellin_convergent (ν s : ℂ) (hs : 0 < s.re)
    (hstrip : s.re+|ν.re| < 1/2) :
    MellinConvergent (spectralWeberKTransform ν) s := by
  have hi := (spectralWeberKMellinKernel_integrable ν s hs hstrip).integral_prod_right
  apply hi.congr
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [smul_eq_mul] using spectralWeberKMellinKernel_integral_x ν s p)

theorem spectralWeberK_mellin (ν s : ℂ) (hs : 0 < s.re)
    (hstrip : s.re+|ν.re| < 1/2) :
    mellin (spectralWeberKTransform ν) s =
      Complex.Gamma s*(2 : ℂ)^(-1-2*s)*Complex.Gamma (1/2-s-ν)*
        Complex.Gamma (1/2-s+ν) := by
  have horder : |(2*ν).re| < (1-2*s).re := by
    norm_num [Complex.mul_re,abs_mul]
    linarith
  have hswap := integral_integral_swap
    (f := fun x p : ℝ => spectralWeberKMellinKernel ν s x p)
    (spectralWeberKMellinKernel_integrable ν s hs hstrip)
  have hleft : (∫ x in Ioi (0 : ℝ), ∫ p in Ioi (0 : ℝ),
      spectralWeberKMellinKernel ν s x p) =
      Complex.Gamma s*(2 : ℂ)^(-1-2*s)*Complex.Gamma (1/2-s-ν)*Complex.Gamma (1/2-s+ν) := by
    calc
      _ = Complex.Gamma s*(∫ x in Ioi (0 : ℝ), (x : ℂ)^((1-2*s)-1)*schlafliBesselK (2*ν) x) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [spectralWeberKMellinKernel_integral_p ν s hs hx,
          show (1 : ℂ)-2*s-1 = -2*s by ring]
      _ = _ := by
        rw [schlafliBesselK_mellin (2*ν) (1-2*s) horder,
          show (1 : ℂ)-2*s-2 = -1-2*s by ring,
          show ((1 : ℂ)-2*s-2*ν)/2 = 1/2-s-ν by ring,
          show ((1 : ℂ)-2*s+2*ν)/2 = 1/2-s+ν by ring]
        ring
  have hright : (∫ p in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ),
      spectralWeberKMellinKernel ν s x p) = mellin (spectralWeberKTransform ν) s := by
    simp_rw [spectralWeberKMellinKernel_integral_x]
    rfl
  exact hright.symm.trans (hswap.symm.trans hleft)

end ArtinMatthews
