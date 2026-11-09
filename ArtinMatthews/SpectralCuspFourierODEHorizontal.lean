module

public import ArtinMatthews.SpectralCuspFourierODEDifferentiation
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts


set_option backward.privateInPublic true
@[expose] public section

/-! Literal integer-frequency phases and genuine periodic integration by
parts on a full horizontal period. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace ArtinMatthews

def cuspFourierFrequency (w : ℝ) (n : ℤ) : ℝ := 2 * Real.pi * n / w

def cuspFourierPhase (w : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I * x)

theorem cuspFourierPhase_contDiff (w : ℝ) (n : ℤ) : ContDiff ℝ ∞ (cuspFourierPhase w n) := by
  unfold cuspFourierPhase
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem cuspFourierPhase_hasDerivAt (w : ℝ) (n : ℤ) (x : ℝ) :
    HasDerivAt (cuspFourierPhase w n)
      (cuspFourierPhase w n x * (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I)) x := by
  simpa only [cuspFourierPhase, id_eq, Complex.ofReal_one, mul_one] using!
    (((hasDerivAt_id x).ofReal_comp).const_mul
      (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I)).cexp

theorem cuspFourierPhase_zero (w : ℝ) (n : ℤ) : cuspFourierPhase w n 0 = 1 := by
  simp only [cuspFourierPhase, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem cuspFourierPhase_period (w : ℝ) (hw : 0 < w) (n : ℤ) : cuspFourierPhase w n w = 1 := by
  have he : -((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I * (w : ℂ) =
      ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold cuspFourierFrequency
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hw.ne']
  rw [cuspFourierPhase, he]
  exact Complex.exp_int_mul_two_pi_mul_I (-n)

theorem spectral_periodic_deriv {f : ℝ → ℂ} {w : ℝ} (h : Function.Periodic f w) :
    Function.Periodic (deriv f) w := by
  intro x
  have he : (fun t => f (t + w)) = f := funext h
  simpa only [deriv_comp_add_const] using congrArg (fun g : ℝ → ℂ => deriv g x) he

theorem cuspFourier_integral_deriv (w : ℝ) (hw : 0 < w) (n : ℤ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f w) :
    (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * deriv f x) =
      (((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I) *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x) := by
  have hχ := cuspFourierPhase_contDiff w n
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => cuspFourierPhase_hasDerivAt w n x)
    (fun x _ => (hf.differentiable (by simp) x).hasDerivAt)
    ((hχ.continuous.mul continuous_const).intervalIntegrable 0 w)
    (hd.continuous.intervalIntegrable 0 w)
  rw [cuspFourierPhase_period w hw n, cuspFourierPhase_zero, one_mul, one_mul,
    show f w = f 0 by simpa only [zero_add] using hp 0, sub_self, zero_sub] at he
  have hfactor :
      (∫ x in (0 : ℝ)..w, (cuspFourierPhase w n x *
        (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I)) * f x) =
      (-((cuspFourierFrequency w n : ℝ) : ℂ) * Complex.I) *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hfactor] at he
  simpa only [neg_mul, neg_neg] using he

theorem cuspFourier_integral_second_deriv (w : ℝ) (hw : 0 < w) (n : ℤ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f w) :
    (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * deriv (deriv f) x) =
      -(((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x)) := by
  rw [cuspFourier_integral_deriv w hw n (deriv f) (contDiff_infty_iff_deriv.mp hf).2
      (spectral_periodic_deriv hp), cuspFourier_integral_deriv w hw n f hf hp]
  calc
    _ = (((cuspFourierFrequency w n : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) *
        (∫ x in (0 : ℝ)..w, cuspFourierPhase w n x * f x) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

end ArtinMatthews
