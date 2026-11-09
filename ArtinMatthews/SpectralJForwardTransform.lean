module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring


set_option backward.privateInPublic true
@[expose] public section

/-! The same-sign forward Bessel transform with the literal removable value
at zero. The integration density is dx/x on the positive ray. -/
noncomputable section
open Set MeasureTheory Complex

namespace ArtinMatthews

def spectralJForwardKernel (z : ℂ) (x : ℝ) : ℂ :=
  if z = 0 then
    -(2 / (Real.pi : ℂ)) * deriv (fun ν : ℂ => Complex.besselJ ν (x : ℂ)) 0
  else
    (Complex.besselJ (-2*I*z) (x : ℂ) - Complex.besselJ (2*I*z) (x : ℂ)) /
      (2*Complex.sin ((Real.pi : ℂ)*I*z))

def spectralJForwardTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), f x*spectralJForwardKernel z x/(x : ℂ)

theorem spectralJForwardKernel_zero (x : ℝ) :
    spectralJForwardKernel 0 x =
      -(2/(Real.pi : ℂ))*deriv (fun ν : ℂ => Complex.besselJ ν (x : ℂ)) 0 := by
  simp [spectralJForwardKernel]

theorem spectralJForwardKernel_of_ne_zero {z : ℂ} (hz : z ≠ 0) (x : ℝ) :
    spectralJForwardKernel z x =
      (Complex.besselJ (-2*I*z) (x : ℂ) - Complex.besselJ (2*I*z) (x : ℂ)) /
        (2*Complex.sin ((Real.pi : ℂ)*I*z)) := by
  simp only [spectralJForwardKernel, ite_eq_right hz]

theorem spectralJForwardKernel_even (x : ℝ) :
    Function.Even (fun z => spectralJForwardKernel z x) := by
  intro z
  change spectralJForwardKernel (-z) x = spectralJForwardKernel z x
  by_cases hz : z = 0
  · simp only [hz, neg_zero]
  · rw [spectralJForwardKernel_of_ne_zero (neg_ne_zero.mpr hz),
      spectralJForwardKernel_of_ne_zero hz,
      show -2*I*(-z) = 2*I*z by ring, show 2*I*(-z) = -2*I*z by ring,
      mul_neg, Complex.sin_neg, mul_neg, div_neg, ← neg_div, neg_sub]

theorem spectralJForwardTransform_even (f : ℝ → ℂ) :
    Function.Even (spectralJForwardTransform f) := by
  intro z
  unfold spectralJForwardTransform
  simp only [spectralJForwardKernel_even _ z]

theorem spectralJForwardKernel_denominator_ne_zero {z : ℂ} (hz : z ≠ 0)
    (hstrip : |z.im| < 1) : 2*Complex.sin ((Real.pi : ℂ)*I*z) ≠ 0 := by
  refine mul_ne_zero (by norm_num) ?_
  intro he
  obtain ⟨n,hn⟩ := Complex.sin_eq_zero_iff.mp he
  have hr := congrArg Complex.re hn
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im] at hr
  have hi : -z.im = (n : ℝ) := mul_left_cancel₀ Real.pi_ne_zero (by nlinarith only [hr])
  have habs : |(n : ℝ)| < 1 := by rw [← hi, abs_neg]; exact hstrip
  have hlo : (-1 : ℤ) < n := by exact_mod_cast (abs_lt.mp habs).1
  have hhi : n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
  have hzero : n = 0 := by omega
  rw [hzero, Int.cast_zero, zero_mul] at hn
  exact (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero) hz) hn

end ArtinMatthews
