module

public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralBesselMellinEvaluation
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The exact Mellin multiplier of the actual sqrt(y) K_nu(qy) model used
by the native cusp Fourier coefficients. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem cuspBesselKernel_mellin_shift (ν s : ℂ) (q y : ℝ) (hy : 0 < y) :
    (y : ℂ)^(s-1)*cuspBesselKernel ν q y =
      (y : ℂ)^((s+1/2)-1)*OAI.CubicEisenstein.schlafliBesselK ν (q*y) := by
  have hsqrt : (Real.sqrt y : ℂ) = (y : ℂ)^(1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow hy.le]
    norm_num
  unfold cuspBesselKernel
  rw [hsqrt,← mul_assoc,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
  congr 2
  ring

theorem cuspBesselKernel_mellin_integrable (ν s : ℂ) {q : ℝ}
    (hq : 0 < q) (hs : |ν.re| < s.re+1/2) :
    IntegrableOn (fun y : ℝ => (y : ℂ)^(s-1)*cuspBesselKernel ν q y) (Ioi 0) := by
  have hshift : |ν.re| < (s+1/2).re := by simpa using hs
  apply (schlafliBesselK_scaled_mellin_integrable ν (s+1/2) hshift hq).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (cuspBesselKernel_mellin_shift ν s q y hy).symm

theorem cuspBesselKernel_mellin (ν s : ℂ) {q : ℝ}
    (hq : 0 < q) (hs : |ν.re| < s.re+1/2) :
    (∫ y in Ioi (0 : ℝ), (y : ℂ)^(s-1)*cuspBesselKernel ν q y) =
      (q : ℂ)^(-s-1/2)*((2 : ℂ)^(s-3/2)*
        Complex.Gamma ((s+1/2-ν)/2)*Complex.Gamma ((s+1/2+ν)/2)) := by
  have hshift : |ν.re| < (s+1/2).re := by simpa using hs
  calc
    _ = ∫ y in Ioi (0 : ℝ), (y : ℂ)^((s+1/2)-1)*
        OAI.CubicEisenstein.schlafliBesselK ν (q*y) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact cuspBesselKernel_mellin_shift ν s q y hy
    _ = _ := by
      convert schlafliBesselK_scaled_mellin ν (s+1/2) hshift hq using 1
      all_goals congr 1 <;> ring

end ArtinMatthews
