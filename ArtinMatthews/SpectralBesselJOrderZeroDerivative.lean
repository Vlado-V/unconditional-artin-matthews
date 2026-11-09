module

public import ArtinMatthews.SpectralBesselJPoissonOrderDerivative
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! The actual complex-order derivative of J at zero, evaluated by the
logarithmic Poisson integral and the exact Gamma half-value. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralBesselJPoissonPrefactor (X : ℝ) (ν : ℂ) : ℂ :=
  ((X : ℂ)/2)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2))

def spectralBesselJZeroLogTerm (X : ℝ) : ℂ :=
  Complex.log ((X : ℂ)/2)-deriv Complex.Gamma (1/2)/Complex.Gamma (1/2)

def spectralBesselJOrderDerivativeZero (X : ℝ) : ℂ :=
  spectralBesselJZeroLogTerm X*Complex.besselJ 0 (X : ℂ)+
    spectralBesselJPoissonDerivativeIntegral X 0/(Real.pi : ℂ)

theorem spectral_besselJ_poisson_denominator_zero :
    (Real.sqrt Real.pi : ℂ)*Complex.Gamma (1/2) = (Real.pi : ℂ) := by
  have hΓ : Complex.Gamma (1/2) = (Real.sqrt Real.pi : ℂ) := by
    simpa only [Nat.cast_zero,zero_add,Nat.mul_zero,Nat.factorial_zero,Nat.cast_one,pow_zero,
      mul_one,one_mul,div_one] using spectral_gamma_nat_add_half 0
  rw [hΓ,← Complex.ofReal_mul,Real.mul_self_sqrt Real.pi_pos.le]

theorem spectralBesselJPoissonPrefactor_zero (X : ℝ) :
    spectralBesselJPoissonPrefactor X 0 = 1/(Real.pi : ℂ) := by
  rw [spectralBesselJPoissonPrefactor,Complex.cpow_zero,zero_add,spectral_besselJ_poisson_denominator_zero]

theorem spectralBesselJPoissonPrefactor_order_hasDerivAt_zero {X : ℝ} (hX : 0 < X) :
    HasDerivAt (spectralBesselJPoissonPrefactor X) (spectralBesselJZeroLogTerm X/(Real.pi : ℂ)) 0 := by
  have hXc : (X : ℂ)/2 ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne') (by norm_num)
  have hN : HasDerivAt (fun ν : ℂ => ((X : ℂ)/2)^ν) (Complex.log ((X : ℂ)/2)) 0 := by
    simpa only [id_eq,Complex.cpow_zero,one_mul,mul_one] using
      (hasDerivAt_id (0 : ℂ)).const_cpow (c := (X : ℂ)/2) (Or.inl hXc)
  have hre : 0 < ((1/2 : ℂ)).re := by norm_num
  have hΓ₀ := Complex.hasDerivAt_Gamma_of_re_pos hre
  have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma (1/2)) (1/2) := by
    rw [hΓ₀.deriv]
    exact hΓ₀
  have harg : HasDerivAt (fun ν : ℂ => ν+1/2) 1 0 := (hasDerivAt_id (0 : ℂ)).add_const (1/2)
  have hD : HasDerivAt (fun ν : ℂ => (Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2))
      ((Real.sqrt Real.pi : ℂ)*deriv Complex.Gamma (1/2)) 0 := by
    simpa only [Function.comp_def,mul_one] using
      (hΓ.comp_of_eq (0 : ℂ) harg (by simp)).const_mul (Real.sqrt Real.pi : ℂ)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hD₀ : (Real.sqrt Real.pi : ℂ)*Complex.Gamma ((0 : ℂ)+1/2) ≠ 0 := by
    rwa [zero_add,spectral_besselJ_poisson_denominator_zero]
  have hG : Complex.Gamma (1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  have hR : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have he : (Complex.log ((X : ℂ)/2)*((Real.sqrt Real.pi : ℂ)*Complex.Gamma ((0 : ℂ)+1/2))-
      (((X : ℂ)/2)^(0 : ℂ))*((Real.sqrt Real.pi : ℂ)*deriv Complex.Gamma (1/2)))/
      (((Real.sqrt Real.pi : ℂ)*Complex.Gamma ((0 : ℂ)+1/2))^2) =
      spectralBesselJZeroLogTerm X/(Real.pi : ℂ) := by
    rw [zero_add,Complex.cpow_zero,one_mul,← spectral_besselJ_poisson_denominator_zero]
    unfold spectralBesselJZeroLogTerm
    field_simp [hG,hR]
  rw [← he]
  exact hN.div hD hD₀

theorem spectral_besselJ_order_hasDerivAt_zero {X : ℝ} (hX : 0 < X) :
    HasDerivAt (fun ν : ℂ => Complex.besselJ ν (X : ℂ)) (spectralBesselJOrderDerivativeZero X) 0 := by
  have hI := spectralBesselJPoissonIntegral_order_hasDerivAt X
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1/8))
  have hP := spectralBesselJPoissonPrefactor_order_hasDerivAt_zero hX
  have he : (fun ν : ℂ => Complex.besselJ ν (X : ℂ)) =ᶠ[𝓝 (0 : ℂ)]
      (fun ν : ℂ => spectralBesselJPoissonPrefactor X ν*spectralBesselJPoissonIntegral X ν) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1/8)] with ν hν
    have hνn : ‖ν‖ < 1/8 := by simpa only [Metric.mem_ball,dist_zero_right] using hν
    have hνre : -(1/2 : ℝ) < ν.re := by linarith [(abs_le.mp (Complex.abs_re_le_norm ν)).1]
    exact spectral_besselJ_poisson_setIntegral X hνre
  have h := (hP.mul hI).congr_of_eventuallyEq he
  have hJ : Complex.besselJ 0 (X : ℂ) =
      spectralBesselJPoissonPrefactor X 0*spectralBesselJPoissonIntegral X 0 :=
    spectral_besselJ_poisson_setIntegral X (by norm_num)
  rw [spectralBesselJPoissonPrefactor_zero] at h hJ
  convert h using 1
  rw [spectralBesselJOrderDerivativeZero,hJ]
  ring_nf

end ArtinMatthews
